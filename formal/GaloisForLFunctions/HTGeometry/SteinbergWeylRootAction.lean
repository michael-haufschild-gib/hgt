import GaloisForLFunctions.HTGeometry.SteinbergWeylConjugation

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F] {n : Type*} [DecidableEq n]

/-- The signed coordinate multiplier induced by one Weyl generator. -/
def steinbergWeylRootScale {i j : n} (u : Fˣ) (p : n) : Fˣ :=
  if p = i then -u⁻¹ else if p = j then u else 1

theorem equiv_swap_ne (i j p q : n) (hpq : p ≠ q) :
    Equiv.swap i j p ≠ Equiv.swap i j q := by
  intro h
  exact hpq ((Equiv.swap i j).injective h)

theorem steinbergWeyl_conj_root_self {i j m : n} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m)
    (u : Fˣ) (a : F) :
    steinbergWeyl hij u * steinbergX hij a * (steinbergWeyl hij u)⁻¹
      = steinbergX (equiv_swap_ne i j i j hij)
          ((steinbergWeylRootScale (i := i) (j := j) u i : F)
            * ((steinbergWeylRootScale (i := i) (j := j) u j)⁻¹ : F) * a) := by
  rw [steinbergWeyl_conj_self hij him hjm]
  simp only [steinbergWeylRootScale, if_pos, if_neg (Ne.symm hij), Units.val_neg,
    Units.val_inv_eq_inv_val, Equiv.swap_apply_left, Equiv.swap_apply_right]
  congr 1
  ring

theorem steinbergWeyl_conj_root_transpose {i j m : n} (hij : i ≠ j) (him : i ≠ m)
    (hjm : j ≠ m) (u : Fˣ) (a : F) :
    steinbergWeyl hij u * steinbergX (Ne.symm hij) a * (steinbergWeyl hij u)⁻¹
      = steinbergX (equiv_swap_ne i j j i (Ne.symm hij))
          ((steinbergWeylRootScale (i := i) (j := j) u j : F)
            * ((steinbergWeylRootScale (i := i) (j := j) u i)⁻¹ : F) * a) := by
  rw [steinbergWeyl_conj_transpose hij him hjm]
  simp only [steinbergWeylRootScale, if_pos, if_neg (Ne.symm hij), Units.val_neg,
    Units.val_inv_eq_inv_val, inv_neg, inv_inv, Equiv.swap_apply_left, Equiv.swap_apply_right]
  congr 1
  ring

theorem steinbergWeyl_conj_root_first {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (u : Fˣ) (a : F) :
    steinbergWeyl hij u * steinbergX hik a * (steinbergWeyl hij u)⁻¹
      = steinbergX (equiv_swap_ne i j i k hik)
          ((steinbergWeylRootScale (i := i) (j := j) u i : F)
            * ((steinbergWeylRootScale (i := i) (j := j) u k)⁻¹ : F) * a) := by
  have hswapk : Equiv.swap i j k = k :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)
  rw [steinbergWeyl_conj_first hij hik hjk]
  simp [steinbergWeylRootScale, hswapk, Ne.symm hik, Ne.symm hjk]

theorem steinbergWeyl_conj_root_second {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (u : Fˣ) (a : F) :
    steinbergWeyl hij u * steinbergX (Ne.symm hjk) a * (steinbergWeyl hij u)⁻¹
      = steinbergX (equiv_swap_ne i j k j (Ne.symm hjk))
          ((steinbergWeylRootScale (i := i) (j := j) u k : F)
            * ((steinbergWeylRootScale (i := i) (j := j) u j)⁻¹ : F) * a) := by
  have hswapk : Equiv.swap i j k = k :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)
  rw [steinbergWeyl_conj_second hij hik hjk]
  simp [steinbergWeylRootScale, hswapk, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  congr 1
  ring

theorem steinbergWeyl_conj_root_row {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (u : Fˣ) (a : F) :
    steinbergWeyl hij u * steinbergX hjk a * (steinbergWeyl hij u)⁻¹
      = steinbergX (equiv_swap_ne i j j k hjk)
          ((steinbergWeylRootScale (i := i) (j := j) u j : F)
            * ((steinbergWeylRootScale (i := i) (j := j) u k)⁻¹ : F) * a) := by
  have hswapk : Equiv.swap i j k = k :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)
  rw [steinbergWeyl_conj_row hij hik hjk]
  simp [steinbergWeylRootScale, hswapk, Ne.symm hij, Ne.symm hik, Ne.symm hjk]

theorem steinbergWeyl_conj_root_col {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (u : Fˣ) (a : F) :
    steinbergWeyl hij u * steinbergX (Ne.symm hik) a * (steinbergWeyl hij u)⁻¹
      = steinbergX (equiv_swap_ne i j k i (Ne.symm hik))
          ((steinbergWeylRootScale (i := i) (j := j) u k : F)
            * ((steinbergWeylRootScale (i := i) (j := j) u i)⁻¹ : F) * a) := by
  have hswapk : Equiv.swap i j k = k :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)
  rw [steinbergWeyl_conj_col hij hik hjk]
  simp [steinbergWeylRootScale, hswapk, Ne.symm hik, Ne.symm hjk]
  congr 1
  ring

theorem steinbergWeyl_conj_root_disjoint {i j p q : n} (hij : i ≠ j) (hpq : p ≠ q)
    (hpi : p ≠ i) (hpj : p ≠ j) (hqi : q ≠ i) (hqj : q ≠ j) (u : Fˣ) (a : F) :
    steinbergWeyl hij u * steinbergX hpq a * (steinbergWeyl hij u)⁻¹
      = steinbergX (equiv_swap_ne i j p q hpq)
          ((steinbergWeylRootScale (i := i) (j := j) u p : F)
            * ((steinbergWeylRootScale (i := i) (j := j) u q)⁻¹ : F) * a) := by
  have hswap_p : Equiv.swap i j p = p := Equiv.swap_apply_of_ne_of_ne hpi hpj
  have hswap_q : Equiv.swap i j q = q := Equiv.swap_apply_of_ne_of_ne hqi hqj
  have hcomm_ij : steinbergX hij (u : F) * steinbergX hpq a
      = steinbergX hpq a * steinbergX hij (u : F) :=
    steinbergX_commute hij hpq (Ne.symm hpj) (Ne.symm hqi) _ _
  have hcomm_ji : steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F)) * steinbergX hpq a
      = steinbergX hpq a * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F)) :=
    steinbergX_commute (Ne.symm hij) hpq (Ne.symm hpi) (Ne.symm hqj) _ _
  have hcommW : steinbergWeyl hij u * steinbergX hpq a
      = steinbergX hpq a * steinbergWeyl hij u := by
    rw [steinbergWeyl]
    calc
      (steinbergX hij (u : F) * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F))
          * steinbergX hij (u : F)) * steinbergX hpq a
        = steinbergX hij (u : F) * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F))
          * (steinbergX hij (u : F) * steinbergX hpq a) := by group
      _ = steinbergX hij (u : F) * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F))
          * (steinbergX hpq a * steinbergX hij (u : F)) := by rw [hcomm_ij]
      _ = steinbergX hij (u : F) *
          (steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F)) * steinbergX hpq a)
          * steinbergX hij (u : F) := by group
      _ = steinbergX hij (u : F) *
          (steinbergX hpq a * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F)))
          * steinbergX hij (u : F) := by rw [hcomm_ji]
      _ = (steinbergX hij (u : F) * steinbergX hpq a)
          * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F)) * steinbergX hij (u : F) := by
          group
      _ = (steinbergX hpq a * steinbergX hij (u : F))
          * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F)) * steinbergX hij (u : F) := by
          rw [hcomm_ij]
      _ = steinbergX hpq a *
          (steinbergX hij (u : F) * steinbergX (Ne.symm hij) (-((u⁻¹ : Fˣ) : F))
            * steinbergX hij (u : F)) := by group
  calc
    steinbergWeyl hij u * steinbergX hpq a * (steinbergWeyl hij u)⁻¹
      = steinbergX hpq a * steinbergWeyl hij u * (steinbergWeyl hij u)⁻¹ := by
        rw [hcommW]
    _ = steinbergX hpq a := by rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = steinbergX (equiv_swap_ne i j p q hpq)
        ((steinbergWeylRootScale (i := i) (j := j) u p : F)
          * ((steinbergWeylRootScale (i := i) (j := j) u q)⁻¹ : F) * a) := by
        simp [steinbergWeylRootScale, hswap_p, hswap_q, hpi, hpj, hqi, hqj]

/-- Exact signed-root action of one Weyl generator.

The permutation part swaps i and j; the coefficient is multiplied by the quotient of
the two signed coordinate weights. -/
theorem steinbergWeyl_conj_root {i j m p q : n} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m)
    (hpq : p ≠ q) (u : Fˣ) (a : F) :
    steinbergWeyl hij u * steinbergX hpq a * (steinbergWeyl hij u)⁻¹
      = steinbergX (equiv_swap_ne i j p q hpq)
          ((steinbergWeylRootScale (i := i) (j := j) u p : F)
            * ((steinbergWeylRootScale (i := i) (j := j) u q)⁻¹ : F) * a) := by
  by_cases hpi : p = i
  · subst p
    by_cases hqj : q = j
    · subst q
      simpa using steinbergWeyl_conj_root_self hij him hjm u a
    · have hiq : i ≠ q := hpq
      have hjq : j ≠ q := Ne.symm hqj
      simpa using steinbergWeyl_conj_root_first hij hiq hjq u a
  · by_cases hpj : p = j
    · subst p
      by_cases hqi : q = i
      · subst q
        simpa using steinbergWeyl_conj_root_transpose hij him hjm u a
      · have hiq : i ≠ q := Ne.symm hqi
        have hjq : j ≠ q := hpq
        simpa using steinbergWeyl_conj_root_row hij hiq hjq u a
    · by_cases hqi : q = i
      · subst q
        have hip : i ≠ p := Ne.symm hpi
        have hjp : j ≠ p := Ne.symm hpj
        simpa using steinbergWeyl_conj_root_col hij hip hjp u a
      · by_cases hqj : q = j
        · subst q
          have hip : i ≠ p := Ne.symm hpi
          have hjp : j ≠ p := Ne.symm hpj
          simpa using steinbergWeyl_conj_root_second hij hip hjp u a
        · exact steinbergWeyl_conj_root_disjoint hij hpq hpi hpj hqi hqj u a

/-- A finite word in Weyl generators, retaining each signed transposition. -/
inductive SteinbergWeylWord (F n : Type*) [Field F] [DecidableEq n] where
  | one : SteinbergWeylWord F n
  | snoc : SteinbergWeylWord F n → (i j : n) → (hij : i ≠ j) → Fˣ → SteinbergWeylWord F n

namespace SteinbergWeylWord

def eval : SteinbergWeylWord F n → SteinbergGroup F n
  | .one => 1
  | .snoc w _ _ hij u => w.eval * steinbergWeyl hij u

def perm : SteinbergWeylWord F n → Equiv.Perm n
  | .one => Equiv.refl n
  | .snoc w i j _ _ => (Equiv.swap i j).trans w.perm

def scale : SteinbergWeylWord F n → n → Fˣ
  | .one => fun _ => 1
  | .snoc w i j _ u => fun p =>
      w.scale (Equiv.swap i j p) * steinbergWeylRootScale (i := i) (j := j) u p

/-- A Weyl word acts on every root by its accumulated signed permutation. -/
theorem conj_root (w : SteinbergWeylWord F n)
    (hspare : ∀ i j : n, i ≠ j → ∃ m : n, i ≠ m ∧ j ≠ m)
    {p q : n} (hpq : p ≠ q) (a : F) :
    w.eval * steinbergX hpq a * w.eval⁻¹
      = steinbergX (w.perm.injective.ne_iff.mpr hpq)
          ((w.scale p : F) * ((w.scale q)⁻¹ : F) * a) := by
  induction w generalizing p q a with
  | one =>
      simp [eval, perm, scale]
  | snoc w i j hij u ih =>
      obtain ⟨m, him, hjm⟩ := hspare i j hij
      have hswap_pq : Equiv.swap i j p ≠ Equiv.swap i j q := equiv_swap_ne i j p q hpq
      have hatomic := steinbergWeyl_conj_root hij him hjm hpq u a
      have hword := ih hswap_pq
        ((steinbergWeylRootScale (i := i) (j := j) u p : F)
          * ((steinbergWeylRootScale (i := i) (j := j) u q)⁻¹ : F) * a)
      calc
        (SteinbergWeylWord.snoc w i j hij u).eval * steinbergX hpq a
            * (SteinbergWeylWord.snoc w i j hij u).eval⁻¹
          = w.eval * (steinbergWeyl hij u * steinbergX hpq a * (steinbergWeyl hij u)⁻¹)
              * w.eval⁻¹ := by
              simp only [eval]
              group
        _ = w.eval * steinbergX hswap_pq
              ((steinbergWeylRootScale (i := i) (j := j) u p : F)
                * ((steinbergWeylRootScale (i := i) (j := j) u q)⁻¹ : F) * a)
              * w.eval⁻¹ := by rw [hatomic]
        _ = steinbergX (w.perm.injective.ne_iff.mpr hswap_pq)
              ((w.scale (Equiv.swap i j p) : F)
                * ((w.scale (Equiv.swap i j q))⁻¹ : F)
                * ((steinbergWeylRootScale (i := i) (j := j) u p : F)
                  * ((steinbergWeylRootScale (i := i) (j := j) u q)⁻¹ : F) * a)) := hword
        _ = steinbergX ((SteinbergWeylWord.snoc w i j hij u).perm.injective.ne_iff.mpr hpq)
              (((SteinbergWeylWord.snoc w i j hij u).scale p : F)
                * (((SteinbergWeylWord.snoc w i j hij u).scale q)⁻¹ : F) * a) := by
              simp only [perm, scale, Equiv.trans_apply, Units.val_mul, mul_inv]
              congr 1
              ring

end SteinbergWeylWord

end GaloisForLFunctions.HTGeometry
