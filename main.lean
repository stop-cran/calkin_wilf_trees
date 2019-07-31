inductive compare : Type
  | eq
  | lt
  | gt

def compare_dec : ℕ → ℕ → compare
| 0 0 := compare.eq
| 0 (nat.succ n) := compare.lt
| (nat.succ m) 0 := compare.gt
| (nat.succ m) (nat.succ n) := compare_dec m n

def compare_dec_eq_iff : Π (m n : ℕ), compare_dec m n = compare.eq ↔ m = n :=
begin
  intros m,
  induction m;
    intro n;
    split;
    intro H;
    cases n;
    try { trivial },

    congr,
    exact (m_ih n).mp H,
    apply (m_ih n).mpr,
    injection H
end

def compare_dec_lt_iff : Π (m n : ℕ), compare_dec m n = compare.lt ↔ m < n :=
begin
  intros m,
  induction m;
    intro n;
    split;
    intro H;
    cases n;
    try { trivial };
    try { exfalso; exact (nat.not_succ_le_zero _ H)},

    apply nat.zero_lt_succ,
    apply nat.succ_lt_succ,
    exact (m_ih _).mp H,
    apply (m_ih _).mpr,
    exact nat.lt_of_succ_lt_succ H
end

def compare_dec_gt_iff : Π (m n : ℕ), compare_dec m n = compare.gt ↔ m > n :=
begin
  intros m,
  induction m;
    intro n;
    split;
    intro H;
    cases n;
    try { trivial };
    try { exfalso; exact (nat.not_succ_le_zero _ H)},

    apply nat.zero_lt_succ,
    apply nat.succ_lt_succ,
    exact (m_ih _).mp H,
    apply (m_ih _).mpr,
    exact nat.lt_of_succ_lt_succ H
end

inductive calkin_wilf : Type 
  | cw_one : calkin_wilf
  | cw_left : calkin_wilf → calkin_wilf
  | cw_right : calkin_wilf → calkin_wilf

open calkin_wilf

inductive cw_rational : Type
| cw_zero : cw_rational
| cw_pos : calkin_wilf → cw_rational
| cw_neg : calkin_wilf → cw_rational

lemma sub_lt2 {m n : ℕ} : m > 0 → n > m → n - m < n :=
begin
  intros Hm Hn,
  cases m,
  exfalso; exact (nat.not_succ_le_zero _ Hm),
  cases n,
  exfalso; exact (nat.not_succ_le_zero _ Hn),
  rewrite nat.succ_sub_succ_eq_sub,
  apply nat.sub_lt_succ
end

lemma succ_n_sub_n_1 (n : ℕ) : nat.succ n - n = 1 :=
begin
  induction n,
  refl,
  rewrite nat.succ_sub_succ_eq_sub,
  assumption
end

lemma succ_succ_n_sub_n_2 (n : ℕ) : nat.succ (nat.succ n) - n = 2 :=
begin
  induction n,
  refl,
  rewrite nat.succ_sub_succ_eq_sub,
  assumption
end

lemma sub_succ_eq {m n : ℕ} : n > m → nat.succ n - m = nat.succ (n - m) :=
begin
  revert n,
  induction m; intros n H,
  refl,
  cases n,
  exfalso,
  exact (nat.not_succ_le_zero _ H),
  simp [nat.succ_sub_succ_eq_sub],
  apply m_ih,
  apply nat.lt_of_succ_lt_succ,
  assumption
end

lemma sub_gt_0 {m n : ℕ} : m > n → m - n > 0 :=
begin
  intro H,
  induction H,
  rewrite succ_n_sub_n_1,
  constructor,
  apply (nat.lt_trans H_ih),
  rewrite sub_succ_eq,
  constructor,
  assumption
end

def cw_to_nat_prod : calkin_wilf → ℕ × ℕ
| cw_one := (1, 1)
| (cw_left cw) := let ⟨m, n⟩ := (cw_to_nat_prod cw) in (m, m + n)
| (cw_right cw) := let ⟨m, n⟩ := (cw_to_nat_prod cw) in (m + n, n)

def nat_prod_to_cw_rec
  (m : ℕ)
  (f : Π  (x : ℕ) (H : x < m) (n' : ℕ)
    (g' : Π  (x : ℕ) (H : x < n') (m' : ℕ), 0 < x → 0 < m' → calkin_wilf), 0 < x → 0 < n' → calkin_wilf)
  (n : ℕ)
  (g : Π  (x : ℕ) (H : x < n) (m' : ℕ), 0 < x → 0 < m' → calkin_wilf)
  (Hm : 0 < m) (Hn : 0 < n) : calkin_wilf :=
begin
  cases eq : (compare_dec m n),
  exact cw_one,

  apply cw_left,
  refine (g m _ (n - m) Hm _),
  exact (compare_dec_lt_iff m n).mp eq,
  apply sub_gt_0,
  exact (compare_dec_lt_iff m n).mp eq,
  
  apply cw_right,
  refine (f (m - n) _ n g _ Hn),
  apply sub_lt2,
  assumption,
  exact (compare_dec_gt_iff m n).mp eq,
  apply sub_gt_0,
  exact (compare_dec_gt_iff m n).mp eq
end

def cw_symmetry : calkin_wilf → calkin_wilf
| cw_one := cw_one
| (cw_left cw) := cw_right (cw_symmetry cw)
| (cw_right cw) := cw_left (cw_symmetry cw)

def nat_prod_to_cw_rec2 (m : ℕ)
  (f : Π  (x : ℕ) (H : x < m) (n' : ℕ), 0 < x → 0 < n' → calkin_wilf)
  (n : ℕ)
  (Hm : 0 < m) (Hn : 0 < n) : calkin_wilf :=
  cw_symmetry ((well_founded.fix nat.lt_wf nat_prod_to_cw_rec) n m f Hn Hm)

def nat_prod_to_cw (m n : nat) (Hm : 0 < m) (Hn : 0 < n) : calkin_wilf :=
  cw_symmetry (well_founded.fix nat.lt_wf nat_prod_to_cw_rec2 n m Hn Hm)

#check nat_prod_to_cw

#reduce cw_to_nat_prod (nat_prod_to_cw 7 28 _ _)