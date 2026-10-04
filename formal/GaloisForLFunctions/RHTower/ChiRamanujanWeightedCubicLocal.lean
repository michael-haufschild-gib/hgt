import GaloisForLFunctions.RHTower.ChiRamanujanCompleteCubicTrace
/-!
# Complete weighted Ramanujan cubic local trace

The coefficient has every signed valuation sector of the damped Ramanujan
family. `weightedLocal_hasSum` evaluates the full complex double sum; its
balanced specialization is the earlier real cubic trace. The six-factor
Euler correction has exact vanishing on both frequency axes. Its mixed
factor, not a positivity argument, supplies the normal-product majorant.
These are arithmetic trace results; no physical diagonal or near-resonance
identification is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

def complexCoefficient (z : ℂ) (i : ℤ) : ℂ :=
  if i = -1 then -z / (1-z) else if 0 ≤ i then 1 else 0

def complexGeometric (x : ℂ) (i : ℤ) : ℂ := if 0 ≤ i then x^i else 0

def complexAtom (k i : ℤ) : ℂ := if i = k then 1 else 0

def complexTail (x : ℂ) (i : ℤ) : ℂ := complexGeometric x i - complexAtom 0 i

def weightedLocal (z x y : ℂ) (v : ℤ × ℤ) : ℂ :=
  complexCoefficient z v.1 * complexCoefficient z v.2 *
    complexCoefficient z (v.1+v.2) * x^v.1 * y^v.2

theorem complexCoefficient_ofReal (z : ℝ) (i : ℤ) :
    complexCoefficient (z : ℂ) i = (coefficient z i : ℂ) := by
  unfold complexCoefficient coefficient
  split_ifs <;> push_cast <;> rfl

theorem weightedLocal_balanced {z : ℝ} (hz : z ≠ 0) (v : ℤ × ℤ) :
    weightedLocal z z z v = (localTriple z v : ℂ) := by
  simp only [weightedLocal, complexCoefficient_ofReal, localTriple, Complex.ofReal_mul,
    Complex.ofReal_zpow, zpow_add₀ (Complex.ofReal_ne_zero.mpr hz)]
  ring

theorem complexGeometric_hasSum {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (complexGeometric x) (1-x)⁻¹ := by
  have hp : HasSum (fun n : ℕ => complexGeometric x n) (1-x)⁻¹ := by
    simpa [complexGeometric] using hasSum_geometric_of_norm_lt_one hx
  have hn : HasSum (fun n : ℕ => complexGeometric x (-(n+1))) 0 := by
    convert hasSum_zero (β := ℕ) (α := ℂ) using 1
    funext n
    have h : ¬ (0 : ℤ) ≤ -(n+1) := by omega
    simp only [complexGeometric, if_neg h]
  simpa using hp.of_nat_of_neg_add_one hn

theorem complexAtom_hasSum (k : ℤ) : HasSum (complexAtom k) 1 := hasSum_ite_eq k 1

theorem complexTail_hasSum {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (complexTail x) ((1-x)⁻¹-1) :=
  (complexGeometric_hasSum hx).sub (complexAtom_hasSum 0)

theorem weightedLocal_decomposition (z x y : ℂ) (i j : ℤ) :
    weightedLocal z x y (i,j) = complexGeometric x i * complexGeometric y j +
      z^2/(1-z)^2 *
        (x⁻¹ * complexAtom (-1) i * complexAtom 0 j +
          y⁻¹ * complexAtom 0 i * complexAtom (-1) j) -
      z/(1-z) * (x⁻¹ * complexAtom (-1) i * complexTail y j +
        y⁻¹ * complexTail x i * complexAtom (-1) j) := by
  by_cases hi : i < -1
  · have hi0 : ¬ 0 ≤ i := by omega
    have hi1 : i ≠ -1 := by omega
    have hiz : i ≠ 0 := by omega
    simp [weightedLocal, complexCoefficient, complexGeometric, complexAtom, complexTail, hi0, hi1, hiz]
  by_cases hj : j < -1
  · have hj0 : ¬ 0 ≤ j := by omega
    have hj1 : j ≠ -1 := by omega
    have hjz : j ≠ 0 := by omega
    simp [weightedLocal, complexCoefficient, complexGeometric, complexAtom, complexTail, hj0, hj1, hjz]
  by_cases hi1 : i = -1
  · subst i
    by_cases hj1 : j = -1
    · subst j
      norm_num [weightedLocal, complexCoefficient, complexGeometric, complexAtom, complexTail]
    by_cases hjz : j = 0
    · subst j
      simp [weightedLocal, complexCoefficient, complexGeometric, complexAtom, complexTail]
      field_simp
      simp
    have hj0 : 0 ≤ j := by omega
    have hsum : 0 ≤ -1+j := by omega
    have hsum1 : -1+j ≠ -1 := by omega
    simp [weightedLocal, complexCoefficient, complexGeometric, complexAtom, complexTail,
      hj1, hjz, hj0, hsum, hsum1]
    ring
  have hi0 : 0 ≤ i := by omega
  by_cases hj1 : j = -1
  · subst j
    by_cases hiz : i = 0
    · subst i
      simp [weightedLocal, complexCoefficient, complexGeometric, complexAtom, complexTail]
      field_simp
      simp
    have hsum : 0 ≤ i + -1 := by omega
    have hsum1 : i + -1 ≠ -1 := by omega
    simp [weightedLocal, complexCoefficient, complexGeometric, complexAtom, complexTail,
      hi1, hiz, hi0, hsum, hsum1]
    ring
  have hj0 : 0 ≤ j := by omega
  have hsum : 0 ≤ i+j := by omega
  have hsum1 : i+j ≠ -1 := by omega
  simp [weightedLocal, complexCoefficient, complexGeometric, complexAtom, complexTail,
    hi1, hj1, hi0, hj0, hsum, hsum1]

private theorem complex_mul_hasSum {X Y : Type} {f : X → ℂ} {g : Y → ℂ} {a b : ℂ}
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun v : X × Y => f v.1*g v.2) (a*b) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

def weightedEuler (z x y : ℂ) : ℂ :=
  1/((1-x)*(1-y)) + (x⁻¹+y⁻¹)*z^2/(1-z)^2 -
    z/(1-z)*(y/(x*(1-y))+x/(y*(1-x)))

theorem weightedLocal_hasSum (z : ℂ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (weightedLocal z x y) (weightedEuler z x y) := by
  have hgx := complexGeometric_hasSum hx
  have hgy := complexGeometric_hasSum hy
  have htx := complexTail_hasSum hx
  have hty := complexTail_hasSum hy
  have hd := complexAtom_hasSum (-1)
  have h0 := complexAtom_hasSum 0
  have h := ((complex_mul_hasSum hgx hgy).add
    ((((complex_mul_hasSum hd h0).mul_left x⁻¹).add
      ((complex_mul_hasSum h0 hd).mul_left y⁻¹)).mul_left (z^2/(1-z)^2))).sub
    ((((complex_mul_hasSum hd hty).mul_left x⁻¹).add
      ((complex_mul_hasSum htx hd).mul_left y⁻¹)).mul_left (z/(1-z)))
  convert h using 1 <;> try rfl
  · funext v
    rw [weightedLocal_decomposition]
    ring
  · have hx0 : 1-x ≠ 0 := by
      intro he
      rw [← sub_eq_zero.mp he, norm_one] at hx
      exact lt_irrefl _ hx
    have hy0 : 1-y ≠ 0 := by
      intro he
      rw [← sub_eq_zero.mp he, norm_one] at hy
      exact lt_irrefl _ hy
    have hxt : (1-x)⁻¹-1 = x/(1-x) := by field_simp; ring
    have hyt : (1-y)⁻¹-1 = y/(1-y) := by field_simp; ring
    rw [hxt, hyt]
    simp only [weightedEuler, div_eq_mul_inv, mul_inv_rev]
    ring

private def ComplexProductSummation (X ι : Type) [Fintype ι] : Prop :=
  ∀ (f : ι → X → ℂ) (a : ι → ℂ), (∀ i, HasSum (f i) (a i)) →
    HasSum (fun x : ι → X => ∏ i, f i (x i)) (∏ i, a i)

private theorem complexProductSummation_equiv {X α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (ih : ComplexProductSummation X α) : ComplexProductSummation X β := by
  classical
  intro f a hf
  have h := ih (fun i => f (e i)) (fun i => a (e i)) (fun i => hf (e i))
  rw [e.prod_comp a] at h
  apply (e.arrowCongr (Equiv.refl X)).hasSum_iff.mp
  refine h.congr_fun ?_
  intro x
  exact (Fintype.prod_equiv e _ _ (fun i => by simp [Equiv.arrowCongr])).symm

private theorem complexProductSummation_empty (X : Type) : ComplexProductSummation X PEmpty.{1} := by
  classical
  intro f a hf
  letI : Fintype (PEmpty.{1} → X) := Fintype.ofSubsingleton (fun x => nomatch x)
  simp

private theorem complexProductSummation_option {X α : Type} [Fintype α]
    (ih : ComplexProductSummation X α) : ComplexProductSummation X (Option α) := by
  classical
  intro f a hf
  have hr := ih (fun i => f (some i)) (fun i => a (some i)) (fun i => hf (some i))
  have h : HasSum (fun v : X × (α → X) => f none v.1 * ∏ i, f (some i) (v.2 i))
      (a none * ∏ i, a (some i)) :=
    HasSum.mul (f := f none) (g := fun v : α → X => ∏ i, f (some i) (v i))
      (hf none) hr
      (summable_mul_of_summable_norm (f := f none)
        (g := fun v : α → X => ∏ i, f (some i) (v i))
        (hf none).summable.norm hr.summable.norm)
  have h' : HasSum (fun v : Option α → X => f none (v none) * ∏ i, f (some i) (v (some i)))
      (a none * ∏ i, a (some i)) :=
    ((Equiv.piOptionEquivProd (β := fun _ : Option α => X)).hasSum_iff
      (f := fun v : X × (α → X) => f none v.1 * ∏ i, f (some i) (v.2 i))).mpr h
  simpa only [Fintype.prod_option] using h'

theorem complex_finite_product_hasSum {X : Type} (ι : Type) [Fintype ι]
    (f : ι → X → ℂ) (a : ι → ℂ) (hf : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun x : ι → X => ∏ i, f i (x i)) (∏ i, a i) :=
  Fintype.induction_empty_option (P := ComplexProductSummation X)
    (fun α β _ e h => by
      letI : Fintype α := Fintype.ofEquiv β e.symm
      exact complexProductSummation_equiv e h) (complexProductSummation_empty X)
    (fun _ _ h => complexProductSummation_option h) ι f a hf

def cubicCorrection (z U V : ℂ) : ℂ :=
  weightedEuler z (z*U) (z*V) * (1-z*U)*(1-z*V)*(1-z/U)*(1-z/V) /
    ((1-z*(V/U))*(1-z*(U/V)))

def cubicMixedNumerator (z U V : ℂ) : ℂ :=
  U+V-1-z^2-U/V-V/U+z/U+z/V

theorem cubicCorrection_mixed_factor {z U V : ℂ}
    (hU : U ≠ 0) (hV : V ≠ 0) (h1 : 1-z ≠ 0)
    (hx : 1-z*U ≠ 0) (hy : 1-z*V ≠ 0)
    (huv : 1-z*(U/V) ≠ 0) (hvu : 1-z*(V/U) ≠ 0) :
    cubicCorrection z U V = 1+
      z^2*(1-U⁻¹)*(1-V⁻¹)*cubicMixedNumerator z U V /
        ((1-z)^2*(1-z*(V/U))*(1-z*(U/V))) := by
  have hu' : U-z*V ≠ 0 := by
    rw [show U-z*V = U*(1-z*(V/U)) by field_simp]
    exact mul_ne_zero hU hvu
  have hv' : V-z*U ≠ 0 := by
    rw [show V-z*U = V*(1-z*(U/V)) by field_simp]
    exact mul_ne_zero hV huv
  have hd : U*V+U*V*z^2-U^2*z-V^2*z ≠ 0 := by
    rw [show U*V+U*V*z^2-U^2*z-V^2*z = (U-z*V)*(V-z*U) by ring]
    exact mul_ne_zero hu' hv'
  unfold cubicCorrection weightedEuler cubicMixedNumerator
  field_simp [hd]
  ring

def cubicRegularFactor (z U V : ℂ) : ℂ := 1+
  z^2*(1-U⁻¹)*(1-V⁻¹)*cubicMixedNumerator z U V /
    ((1-z)^2*(1-z*(V/U))*(1-z*(U/V)))

theorem norm_cubicMixedNumerator_le {z U V : ℂ} {r : ℝ} (hr : 1 ≤ r)
    (hz : ‖z‖ ≤ 1) (hU : ‖U‖ ≤ r) (hV : ‖V‖ ≤ r)
    (hUi : ‖U⁻¹‖ ≤ r) (hVi : ‖V⁻¹‖ ≤ r) :
    ‖cubicMixedNumerator z U V‖ ≤ 8*r^2 := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hr2 : r ≤ r^2 := by nlinarith
  have hz2 : ‖z^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hUV : ‖U/V‖ ≤ r^2 := by
    rw [div_eq_mul_inv, norm_mul, pow_two]
    exact mul_le_mul hU hVi (norm_nonneg _) hr0
  have hVU : ‖V/U‖ ≤ r^2 := by
    rw [div_eq_mul_inv, norm_mul, pow_two]
    exact mul_le_mul hV hUi (norm_nonneg _) hr0
  have hzU : ‖z/U‖ ≤ r := by
    rw [div_eq_mul_inv, norm_mul]
    simpa using mul_le_mul hz hUi (norm_nonneg _) zero_le_one
  have hzV : ‖z/V‖ ≤ r := by
    rw [div_eq_mul_inv, norm_mul]
    simpa using mul_le_mul hz hVi (norm_nonneg _) zero_le_one
  have h1 := norm_add_le U V
  have h2 := norm_sub_le (U+V) (1 : ℂ)
  have h3 := norm_sub_le (U+V-1) (z^2)
  have h4 := norm_sub_le (U+V-1-z^2) (U/V)
  have h5 := norm_sub_le (U+V-1-z^2-U/V) (V/U)
  have h6 := norm_add_le (U+V-1-z^2-U/V-V/U) (z/U)
  have h7 := norm_add_le (U+V-1-z^2-U/V-V/U+z/U) (z/V)
  rw [norm_one] at h2
  dsimp only [cubicMixedNumerator]
  linarith

theorem norm_cubicRegularFactor_sub_one_le {z U V : ℂ} {a c r : ℝ}
    (hr : 1 ≤ r) (hc : c < 1) (hz : ‖z‖ ≤ a) (hzc : ‖z‖ ≤ c)
    (hU : ‖U‖ ≤ r) (hV : ‖V‖ ≤ r) (hUi : ‖U⁻¹‖ ≤ r) (hVi : ‖V⁻¹‖ ≤ r)
    (hUV : ‖z*(U/V)‖ ≤ c) (hVU : ‖z*(V/U)‖ ≤ c) :
    ‖cubicRegularFactor z U V-1‖ ≤ 32*a^2*r^4/(1-c)^4 := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hc0 : 0 < 1-c := sub_pos.mpr hc
  have hz1 : ‖z‖ ≤ 1 := hzc.trans hc.le
  have hn := norm_cubicMixedNumerator_le hr hz1 hU hV hUi hVi
  have hu1 : ‖1-U⁻¹‖ ≤ 2*r := by
    have h := norm_sub_le (1 : ℂ) U⁻¹
    rw [norm_one] at h
    linarith
  have hv1 : ‖1-V⁻¹‖ ≤ 2*r := by
    have h := norm_sub_le (1 : ℂ) V⁻¹
    rw [norm_one] at h
    linarith
  have hd1 : 1-c ≤ ‖1-z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at h
    linarith
  have hd2 : 1-c ≤ ‖1-z*(V/U)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (z*(V/U))
    rw [norm_one] at h
    linarith
  have hd3 : 1-c ≤ ‖1-z*(U/V)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (z*(U/V))
    rw [norm_one] at h
    linarith
  have hden : (1-c)^4 ≤ ‖(1-z)^2*(1-z*(V/U))*(1-z*(U/V))‖ := by
    rw [norm_mul, norm_mul, norm_pow]
    calc
      (1-c)^4 = (1-c)^2*(1-c)*(1-c) := by ring
      _ ≤ ‖1-z‖^2*‖1-z*(V/U)‖*‖1-z*(U/V)‖ := by gcongr
  have hnum : ‖z^2*(1-U⁻¹)*(1-V⁻¹)*cubicMixedNumerator z U V‖ ≤ 32*a^2*r^4 := by
    simp only [norm_mul, norm_pow]
    calc
      _ ≤ a^2*(2*r)*(2*r)*(8*r^2) := by gcongr
      _ = _ := by ring
  unfold cubicRegularFactor
  rw [add_sub_cancel_left, norm_div]
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)

end RHTower.BAGTrace
