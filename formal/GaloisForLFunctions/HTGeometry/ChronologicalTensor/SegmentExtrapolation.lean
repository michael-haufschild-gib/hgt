import GaloisForLFunctions.HTGeometry.ChronologicalTensor.Sealing
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.ChebyshevGrowth

/-!
# Extrapolating between monotone probes

The restriction of a homogeneous window form to a segment between two monotone
unit probes is an actual univariate polynomial of the original degree or less.
Mathlib's classical Chebyshev extremal theorem controls extrapolation beyond the
segment, including the identically zero observational class.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Finset

def segmentParameter (t : ℝ) : ℝ := max (-1) (min t 1)

theorem segmentParameter_bounds (t : ℝ) : -1 ≤ segmentParameter t ∧ segmentParameter t ≤ 1 :=
  ⟨le_max_left _ _,max_le (by linarith) (min_le_right _ _)⟩

def segmentProbe {n : ℕ} (g h : Fin (n+1) → ℝ) (t : ℝ) : Fin (n+1) → ℝ :=
  fun i => ((1+t)/2)*radialProbe g i+((1-t)/2)*radialProbe h i

theorem segmentProbe_data {n : ℕ} (g h : Fin (n+1) → ℝ) (t : ℝ) :
    (∀ i, 0 ≤ segmentProbe g h (segmentParameter t) i) ∧
      variation (segmentProbe g h (segmentParameter t)) = 1 := by
  have ht := segmentParameter_bounds t
  have hgn := (radialProbe_data g).1
  have hhn := (radialProbe_data h).1
  have hn (i : Fin (n+1)) : 0 ≤ segmentProbe g h (segmentParameter t) i := by
    exact add_nonneg (mul_nonneg (by linarith) (hgn i)) (mul_nonneg (by linarith) (hhn i))
  refine ⟨hn,?_⟩
  simp only [variation]
  simp_rw [abs_of_nonneg (hn _)]
  simp only [segmentProbe,sum_add_distrib,← mul_sum]
  change ((1+segmentParameter t)/2)*displacement (radialProbe g)+
    ((1-segmentParameter t)/2)*displacement (radialProbe h) = 1
  rw [(radialProbe_data g).2.1,(radialProbe_data h).2.1]
  ring

theorem segmentProbe_bound {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (g h : Fin (n+1) → ℝ) (t : ℝ) :
    |familyValue D c (segmentProbe g h (segmentParameter t))| ≤ monotoneCapacity D c := by
  let p := segmentProbe g h (segmentParameter t)
  have hd := segmentProbe_data g h t
  have hf : normalizeProbe p = p := (normalizeProbe_fixed_iff p).mpr (le_of_eq hd.2)
  have hm : monotoneProbe p = p := by
    funext i
    simp only [monotoneProbe,hf]
    exact abs_of_nonneg (hd.1 i)
  have hb := monotoneCapacity_probe_bound D c p
  rwa [hm] at hb

def segmentPolynomial {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (g h : Fin (n+1) → ℝ) : Polynomial ℝ :=
  ∑ j, Polynomial.C (c j)*∏ k,
    (Polynomial.C ((windowValue (D j k) (radialProbe g)+windowValue (D j k) (radialProbe h))/2)+
      Polynomial.X*Polynomial.C ((windowValue (D j k) (radialProbe g)-
        windowValue (D j k) (radialProbe h))/2))

theorem windowValue_segmentProbe {n : ℕ} (W : Finset (Fin (n+1)))
    (g h : Fin (n+1) → ℝ) (t : ℝ) :
    windowValue W (segmentProbe g h t) = ((1+t)/2)*windowValue W (radialProbe g)+
      ((1-t)/2)*windowValue W (radialProbe h) := by
  simp only [windowValue,segmentProbe,sum_add_distrib,← mul_sum]

theorem segmentPolynomial_eval {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (g h : Fin (n+1) → ℝ) (t : ℝ) :
    (segmentPolynomial D c g h).eval t = familyValue D c (segmentProbe g h t) := by
  simp only [segmentPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_X,familyValue,diagramValue]
  apply sum_congr rfl
  intro j _
  congr 1
  apply prod_congr rfl
  intro k _
  rw [windowValue_segmentProbe]
  ring

theorem segmentPolynomial_degree {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (g h : Fin (n+1) → ℝ) : (segmentPolynomial D c g h).natDegree ≤ r := by
  unfold segmentPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply Polynomial.natDegree_mul_le.trans
  rw [Polynomial.natDegree_C,zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ (_ : Fin r), 1 := by
      apply sum_le_sum
      intro k _
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · apply Polynomial.natDegree_mul_le.trans
        simp
    _ = r := by simp


theorem familyValue_normalize_scale {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) :
    familyValue D c g = max 1 (variation g)^r*familyValue D c (normalizeProbe g) := by
  have hd : 0 < max 1 (variation g) := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have he : g = fun i => max 1 (variation g)*normalizeProbe g i := by
    funext i
    dsimp [normalizeProbe]
    field_simp
  calc
    familyValue D c g = familyValue D c (fun i => max 1 (variation g)*normalizeProbe g i) :=
      congrArg (familyValue D c) he
    _ = _ := familyValue_scale D c _ _

theorem segment_extrapolation {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin (n+1)))
    (c : Fin m → ℝ) (g h : Fin (n+1) → ℝ) (t : ℝ) :
    |familyValue D c (segmentProbe g h (1+|t|))| ≤ monotoneCapacity D c*(1+|t|)^(r*r) := by
  by_cases hm : monotoneCapacity D c = 0
  · have hf := (monotoneCapacity_zero_iff D c).mp hm
    rw [familyValue_normalize_scale,(familyCapacity_zero_iff D c).mp hf,mul_zero,abs_zero,hm,zero_mul]
  · have hp : 0 < monotoneCapacity D c :=
      lt_of_le_of_ne (monotoneCapacity_nonneg D c) (Ne.symm hm)
    let Q := Polynomial.C ((monotoneCapacity D c)⁻¹)*segmentPolynomial D c g h
    have hdeg : Q.degree ≤ r := by
      apply Polynomial.degree_le_of_natDegree_le
      apply Polynomial.natDegree_mul_le.trans
      simp only [Polynomial.natDegree_C,zero_add]
      exact segmentPolynomial_degree D c g h
    have hQ : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |Q.eval x| ≤ 1 := by
      intro x hx
      have he : segmentParameter x = x := by
        rw [segmentParameter,min_eq_left hx.2,max_eq_right hx.1]
      have hb := segmentProbe_bound D c g h x
      rw [he] at hb
      have hh := (div_le_one hp).mpr hb
      simpa [Q,Polynomial.eval_mul,Polynomial.eval_C,segmentPolynomial_eval,
        abs_mul,abs_of_pos hp,div_eq_mul_inv,mul_comm] using hh
    have hx : (1 : ℝ) ≤ 1+|t| := by linarith [abs_nonneg t]
    have hu := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (k := 0) hx hdeg hQ
    have hl := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (k := 0) hx (show (-Q).degree ≤ r by simpa only [Polynomial.degree_neg] using hdeg)
      (show ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(-Q).eval x| ≤ 1 by
        intro x hx; simpa only [Polynomial.eval_neg,abs_neg] using hQ x hx)
    simp only [Function.iterate_zero, id_eq,Polynomial.eval_neg] at hu hl
    have hb := (abs_le.mpr ⟨by linarith,hu⟩).trans (chebyshev_power_bound t r)
    have hh : |familyValue D c (segmentProbe g h (1+|t|))|/monotoneCapacity D c ≤
        (1+|t|)^(r*r) := by
      simpa [Q,Polynomial.eval_mul,Polynomial.eval_C,segmentPolynomial_eval,
        abs_mul,abs_of_pos hp,div_eq_mul_inv,mul_comm] using hb
    have he := (div_le_iff₀ hp).mp hh
    simpa only [mul_comm] using he


end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
