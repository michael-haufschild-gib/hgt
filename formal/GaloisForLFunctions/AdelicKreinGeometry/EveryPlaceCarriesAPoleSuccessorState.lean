import GaloisForLFunctions.AdelicKreinGeometry.TheHeckeBoostAndTheConformalSuccessorAreOneState
import GaloisForLFunctions.AdelicKreinGeometry.TheFunctionFieldConformalSuccessor
import Mathlib.NumberTheory.Ostrowski

/-!
# Every place carries a pole–successor state

For a nonarchimedean absolute value `v` of a field `K` the balls `{z : |z|_v ≤ r}` are additive
subgroups, so `1[|x − y|_v ≤ r]` is an equivalence kernel, hence positive
(`re_sum_ite_ball_nonneg`).

* **Layer cake** (`integral_indicator_Ici_eq`): `R − t = ∫_0^R 1[t ≤ r] dr` for `0 ≤ t ≤ R`, so on
  a polar vector the form of `−|·|_v` is `∫_0^R` of ball forms.
* **Ultrametric successors are conditionally positive** (`hermQuad_gram_negUltra_nonneg`): for every
  nonarchimedean `v`, `−|b|_v` is nonnegative on the polar hyperplane.
* **The local pole–successor state** (`negIndex_poleSuccessor_negUltra`): for a nontrivial
  nonarchimedean `v` and `c ≥ 0`, `|a|_v^{1/2} + |a|_v^{−1/2} − c|a|_v^{−1/2}|b|_v` has exactly one
  negative square; at the prime `p` the boost pair is `p^{∓k/2}` on `p^k`
  (`negIndex_padicPoleSuccessor`).
* **Conformal induction at `p`** (`negIndex_padicInduction`): `−|a|_p^{−1/2}|b|_p` has index one.
* **Calibration over `F(X)`** (`negIndex_inftyPoleSuccessor`, `inftyPoleSuccessor_dilation_X`): the
  place at infinity `|f|_∞ = b^{deg f}` is ultrametric (`isUltra_inftyAbs`); its pole–successor state
  has index one and the dilation by `X` is the boost `b^{1/2} + b^{−1/2}`, over `𝔽_q` the Frobenius
  eigenvalues `1, q` on `H⁰`, `H²` after the twist by `q^{−1/2}`.

So each place of `ℚ`, archimedean (`negIndex_poleSuccessorState`) or `p`-adic, carries its own
index-one state with a boost on `ℚ^×` and a conformal successor on `ℚ`; this is the local
signature `1` at every place. By the product formula `∏_v |a|_v = 1` the local boosts multiply to
`1` on `ℚ^×`: the pole pairs live place by place, and their product is not a boost.
-/

open Complex Finset MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {K : Type*} [Field K]

/-- Nonarchimedean absolute values. -/
def IsUltra (v : AbsoluteValue K ℝ) : Prop := ∀ x y : K, v (x + y) ≤ max (v x) (v y)

/-- The ball `{z : |z|_v ≤ r}` is an additive subgroup. -/
def ballSubgroup {v : AbsoluteValue K ℝ} (hv : IsUltra v) {r : ℝ} (hr : 0 ≤ r) : AddSubgroup K where
  carrier := {z | v z ≤ r}
  zero_mem' := by simp [hr]
  add_mem' {x y} hx hy := (hv x y).trans (max_le hx hy)
  neg_mem' {x} hx := by simpa [Set.mem_setOf_eq, AbsoluteValue.map_neg] using hx

/-- **Ball kernels are positive**: `1[|x_b − x_a|_v ≤ r]` is the kernel of an equivalence. -/
theorem re_sum_ite_ball_nonneg {v : AbsoluteValue K ℝ} (hv : IsUltra v) {r : ℝ} (hr : 0 ≤ r)
    {n : ℕ} (x : Fin n → K) (c : Fin n → ℂ) :
    0 ≤ (∑ a, ∑ b, conj (c a) * c b * (if v (-x a + x b) ≤ r then 1 else 0)).re := by
  classical
  have h := re_sum_ite_eq_nonneg (fun a => (QuotientAddGroup.mk (x a) : K ⧸ ballSubgroup hv hr)) c
  have e : ∀ a b, ((QuotientAddGroup.mk (x a) : K ⧸ ballSubgroup hv hr) = QuotientAddGroup.mk (x b))
      ↔ v (-x a + x b) ≤ r := fun a b => QuotientAddGroup.eq
  simpa only [e] using h

/-- **Layer cake**: `R − t = ∫_0^R 1[t ≤ r] dr`. -/
theorem integral_indicator_Ici_eq {t R : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) :
    ∫ r in Set.Icc 0 R, (Set.Ici t).indicator (fun _ => (1 : ℝ)) r = R - t := by
  have e : Set.Ici t ∩ Set.Icc 0 R = Set.Icc t R := Set.ext fun r => by
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ht.trans h.1, h.2⟩⟩
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici, e,
    setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]

/-- The successor `−|b|_v`. -/
def negUltra (v : AbsoluteValue K ℝ) (m : Multiplicative K) : ℂ :=
  -((v (Multiplicative.toAdd m) : ℝ) : ℂ)

/-- **Ultrametric successors are conditionally positive.** -/
theorem hermQuad_gram_negUltra_nonneg {v : AbsoluteValue K ℝ} (hv : IsUltra v) {n : ℕ}
    (x : Fin n → Multiplicative K) (c : Fin n → ℂ) (hc : ∑ a, c a = 0) :
    0 ≤ hermQuad (gram (negUltra v) x) c := by
  set y : Fin n → K := fun a => Multiplicative.toAdd (x a)
  set z : Fin n → Fin n → ℝ := fun a b => v (-y a + y b)
  set ρ : Fin n → Fin n → ℝ := fun a b => (conj (c a) * c b).re
  set R : ℝ := ∑ a, ∑ b, z a b
  have hz0 : ∀ a b, 0 ≤ z a b := fun a b => v.nonneg _
  have hzR : ∀ a b, z a b ≤ R := fun a b =>
    ((single_le_sum (f := fun b => z a b) (fun b _ => hz0 a b) (mem_univ b))).trans
      (single_le_sum (f := fun a => ∑ b, z a b) (fun a _ => sum_nonneg fun b _ => hz0 a b)
        (mem_univ a))
  have hmass : ∑ a, ∑ b, ρ a b = 0 := by
    simp only [ρ, ← Complex.re_sum]
    rw [← sum_mul_sum, ← map_sum, hc, map_zero, zero_mul, Complex.zero_re]
  -- the form as a real double sum
  have hform : hermQuad (gram (negUltra v) x) c = ∑ a, ∑ b, ρ a b * (R - z a b) := by
    rw [hermQuad_gram, Complex.re_sum]
    simp_rw [Complex.re_sum]
    have e : ∀ a b, (conj (c a) * negUltra v ((x a)⁻¹ * x b) * c b).re = ρ a b * (R - z a b) -
        R * ρ a b := fun a b => by
      simp only [negUltra, toAdd_mul, toAdd_inv, z, y, ρ]
      rw [show conj (c a) * -((v (-Multiplicative.toAdd (x a) + Multiplicative.toAdd (x b)) : ℝ) : ℂ)
          * c b = ((-v (-Multiplicative.toAdd (x a) + Multiplicative.toAdd (x b)) : ℝ) : ℂ) *
            (conj (c a) * c b) by push_cast; ring, Complex.re_ofReal_mul]
      ring
    simp_rw [e, sum_sub_distrib, ← mul_sum, hmass, mul_zero, sub_zero]
  -- layer cake and positivity of ball kernels
  have hlayer : ∑ a, ∑ b, ρ a b * (R - z a b) =
      ∫ r in Set.Icc 0 R, ∑ a, ∑ b, ρ a b * (Set.Ici (z a b)).indicator (fun _ => (1 : ℝ)) r := by
    have hint : ∀ a b, Integrable (fun r => ρ a b * (Set.Ici (z a b)).indicator (fun _ => (1 : ℝ)) r)
        (volume.restrict (Set.Icc 0 R)) := fun a b =>
      ((integrable_const (1 : ℝ)).indicator measurableSet_Ici).const_mul _
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
    refine sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hint a b]
    refine sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_indicator_Ici_eq (hz0 a b) (hzR a b)]
  rw [hform, hlayer]
  refine setIntegral_nonneg measurableSet_Icc fun r hr => ?_
  have h := re_sum_ite_ball_nonneg hv hr.1 y c
  rw [Complex.re_sum] at h
  simp_rw [Complex.re_sum] at h
  refine h.trans_eq (sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_)
  simp only [Set.indicator, Set.mem_Ici, ρ, z]
  split_ifs <;> simp

/-- Ultrametric successors are conformal of exponent `1`. -/
theorem isConformal_negUltra (v : AbsoluteValue K ℝ) (c : ℝ) :
    IsConformal v 1 fun m => (c : ℂ) * negUltra v m := fun u b _ => by
  simp only [negUltra, toAdd_ofAdd, map_mul, Real.rpow_one]
  push_cast
  ring

/-- **The local pole–successor state** at a nonarchimedean place has exactly one negative
square. -/
theorem negIndex_poleSuccessor_negUltra {v : AbsoluteValue K ℝ} (hv : IsUltra v)
    (hnt : ∃ u : K, 1 < v u) {c : ℝ} (hc : 0 ≤ c) :
    negIndex (poleSuccessor v 1 fun m => (c : ℂ) * negUltra v m) = 1 :=
  negIndex_poleSuccessor one_pos hnt (isConformal_negUltra v c) fun n x w hw => by
    have e : gram (fun m => (c : ℂ) * negUltra v m) x = (c : ℂ) • gram (negUltra v) x := by
      ext a b; simp [gram]
    rw [e, hermQuad_smul]
    exact mul_nonneg hc (hermQuad_gram_negUltra_nonneg hv x w hw)

section Padic

variable (p : ℕ) [Fact p.Prime]

theorem isUltra_padic : IsUltra (Rat.AbsoluteValue.padic p) := fun x y => by
  simp only [Rat.AbsoluteValue.padic_eq_padicNorm]
  exact_mod_cast padicNorm.nonarchimedean

/-- `|1/p|_p = p > 1`. -/
theorem one_lt_padic_inv : 1 < Rat.AbsoluteValue.padic p (p : ℚ)⁻¹ := by
  rw [map_inv₀, Rat.AbsoluteValue.padic_eq_padicNorm, padicNorm.padicNorm_p_of_prime]
  push_cast
  rw [inv_inv]
  exact_mod_cast (Fact.out : p.Prime).one_lt

/-- **The `p`-adic pole–successor state** `|a|_p^{1/2} + |a|_p^{−1/2} − c|a|_p^{−1/2}|b|_p` has
exactly one negative square. -/
theorem negIndex_padicPoleSuccessor {c : ℝ} (hc : 0 ≤ c) :
    negIndex (poleSuccessor (Rat.AbsoluteValue.padic p) 1
      fun m => (c : ℂ) * negUltra (Rat.AbsoluteValue.padic p) m) = 1 :=
  negIndex_poleSuccessor_negUltra (isUltra_padic p) ⟨_, one_lt_padic_inv p⟩ hc

/-- **Conformal induction at `p`**: `−|a|_p^{−1/2}|b|_p` has exactly one negative square. -/
theorem negIndex_padicInduction :
    negIndex (conformalInduction (Rat.AbsoluteValue.padic p) 1
      (negUltra (Rat.AbsoluteValue.padic p))) = 1 := by
  have hconf : IsConformal (Rat.AbsoluteValue.padic p) 1 (negUltra (Rat.AbsoluteValue.padic p)) := by
    simpa using isConformal_negUltra (Rat.AbsoluteValue.padic p) 1
  rw [negIndex_conformalInduction hconf]
  refine le_antisymm ?_ ?_
  · have hpol : polarIndex (negUltra (Rat.AbsoluteValue.padic p)) = 0 :=
      nonpos_iff_eq_zero.mp (iSup₂_le fun n x => by
        rw [negIndexOn_eq_zero_of_nonneg fun c hc =>
          hermQuad_gram_negUltra_nonneg (isUltra_padic p) x c hc]
        rfl)
    simpa [hpol] using negIndex_le_polarIndex_add_one (negUltra (Rat.AbsoluteValue.padic p))
  · -- `0` and `1`: the Gram matrix `[[0, −1], [−1, 0]]`
    have hneg : hermQuad (gram (negUltra (Rat.AbsoluteValue.padic p))
        ![1, Multiplicative.ofAdd 1]) ![1, 1] < 0 := by
      rw [hermQuad_gram]
      simp [Fin.sum_univ_two, negUltra]
    simpa using card_le_negIndex_of_orthogonal_translates (J := Fin 1) hneg (fun _ => 1)
      fun j j' h => absurd (Subsingleton.elim j j') h

end Padic

/-! ### The place at infinity of `F(X)` -/

section Infinity

open scoped Classical

variable {F : Type*} [Field F] {b : ℝ}

/-- `|f|_∞ = b^{deg f}` on `F(X)`, `deg = deg num − deg den`, and `|0|_∞ = 0`. -/
def inftyNorm (b : ℝ) (f : RatFunc F) : ℝ := if f = 0 then 0 else b ^ f.intDegree

theorem inftyNorm_nonneg (hb : 1 < b) (f : RatFunc F) : 0 ≤ inftyNorm b f := by
  unfold inftyNorm
  split_ifs
  exacts [le_rfl, zpow_nonneg (by linarith) _]

/-- The ultrametric inequality at infinity: `deg (f + g) ≤ max (deg f) (deg g)`. -/
theorem inftyNorm_add_le (hb : 1 < b) (f g : RatFunc F) :
    inftyNorm b (f + g) ≤ max (inftyNorm b f) (inftyNorm b g) := by
  by_cases hfg : f + g = 0
  · rw [inftyNorm, if_pos hfg]; exact le_max_of_le_left (inftyNorm_nonneg hb f)
  by_cases hg : g = 0
  · subst hg; rw [add_zero]; exact le_max_left _ _
  by_cases hf : f = 0
  · subst hf; rw [zero_add]; exact le_max_right _ _
  rw [inftyNorm, inftyNorm, inftyNorm, if_neg hfg, if_neg hf, if_neg hg]
  have hmono : Monotone fun n : ℤ => b ^ n := fun m n h => zpow_le_zpow_right₀ hb.le h
  rw [← hmono.map_max]
  exact zpow_le_zpow_right₀ hb.le (RatFunc.intDegree_add_le hg hfg)

/-- **The place at infinity of `F(X)`**; for `F = 𝔽_q`, `b = q`. -/
def inftyAbs (hb : 1 < b) : AbsoluteValue (RatFunc F) ℝ where
  toFun := inftyNorm b
  map_mul' f g := by
    unfold inftyNorm
    by_cases hf : f = 0
    · simp [hf]
    by_cases hg : g = 0
    · simp [hg]
    rw [if_neg (mul_ne_zero hf hg), if_neg hf, if_neg hg, RatFunc.intDegree_mul hf hg,
      zpow_add₀ (by linarith : (0 : ℝ) < b).ne']
  nonneg' := inftyNorm_nonneg hb
  eq_zero' f := by
    unfold inftyNorm
    constructor
    · intro h
      by_contra hf
      rw [if_neg hf] at h
      exact (zpow_pos (by linarith : (0 : ℝ) < b) _).ne' h
    · intro h; simp [h]
  add_le' f g := (inftyNorm_add_le hb f g).trans
    (max_le (le_add_of_nonneg_right (inftyNorm_nonneg hb g))
      (le_add_of_nonneg_left (inftyNorm_nonneg hb f)))

theorem inftyAbs_apply (hb : 1 < b) {f : RatFunc F} (hf : f ≠ 0) :
    inftyAbs hb f = b ^ f.intDegree := if_neg hf

theorem isUltra_inftyAbs (hb : 1 < b) : IsUltra (inftyAbs (F := F) hb) := inftyNorm_add_le hb

/-- `|X|_∞ = b`. -/
theorem inftyAbs_X (hb : 1 < b) : inftyAbs (F := F) hb RatFunc.X = b := by
  rw [inftyAbs_apply hb RatFunc.X_ne_zero, RatFunc.intDegree_X, zpow_one]

/-- **The pole–successor state of `F(X)` at infinity** has exactly one negative square; the
dilation by `X` is the boost `b^{1/2} + b^{−1/2}` (`q^{±1/2}` over `𝔽_q`). -/
theorem negIndex_inftyPoleSuccessor (hb : 1 < b) {c : ℝ} (hc : 0 ≤ c) :
    negIndex (poleSuccessor (inftyAbs (F := F) hb) 1
      fun m => (c : ℂ) * negUltra (inftyAbs hb) m) = 1 :=
  negIndex_poleSuccessor_negUltra (isUltra_inftyAbs hb) ⟨RatFunc.X, by rw [inftyAbs_X]; exact hb⟩ hc

theorem inftyPoleSuccessor_dilation_X (hb : 1 < b) (c : ℝ) :
    poleSuccessor (inftyAbs (F := F) hb) 1 (fun m => (c : ℂ) * negUltra (inftyAbs hb) m)
      (dilationOf (Units.mk0 RatFunc.X RatFunc.X_ne_zero)) =
      ((b ^ (1 / 2 : ℝ) + (b ^ (1 / 2 : ℝ))⁻¹ : ℝ) : ℂ) := by
  rw [poleSuccessor_dilation one_pos ⟨RatFunc.X, by rw [inftyAbs_X]; exact hb⟩
    (isConformal_negUltra _ c), Units.val_mk0, inftyAbs_X]

end Infinity

end GaloisForLFunctions.AdelicKreinGeometry
