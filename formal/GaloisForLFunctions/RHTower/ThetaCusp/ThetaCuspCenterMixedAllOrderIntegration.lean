import GaloisForLFunctions.HTGeometry.AlternatingPairJetIntegral
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeSixthRankBoundary
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedSignedJetCompleteness

/-!
# Literal all-order center integration

Every center-mixed theta derivative is the integral of the corresponding native
reflection derivative. The signed finite Hankel forms therefore retain center
integration exactly, at every order and every critical aperture.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

/-- All iterated derivatives of every weighted derivative product are integrable. -/
theorem integrable_iteratedDeriv_thetaCuspCenterMixedDerivativeProduct
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (k m n : ℕ) (t : ℝ) :
    IntegrableOn (fun r => iteratedDeriv k (thetaCuspCenterMixedDerivativeProduct m n a r) t)
      (Ioi 0) := by
  have hjet (r : ℝ) := iteratedDeriv_eq_alternatingPairJet
    (fun m n => thetaCuspCenterMixedDerivativeProduct m n a r)
    (fun m n t => hasDerivAt_thetaCuspCenterMixedDerivativeProduct m n a r t) k m n
  simp_rw [hjet]
  exact integrable_alternatingPairJet
    (fun m n r => thetaCuspCenterMixedDerivativeProduct m n a r t)
    (fun m n => integrable_thetaCuspCenterMixedDerivativeProduct ha0 ha m n) k m n

/-- Differentiation under the physical center integral at every order. -/
theorem iteratedDeriv_thetaCuspCenterMixedDerivativeProductIntegral
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (k m n : ℕ) (t : ℝ) :
    iteratedDeriv k (thetaCuspCenterMixedDerivativeProductIntegral m n a) t =
      ∫ r : ℝ in Ioi 0, iteratedDeriv k (thetaCuspCenterMixedDerivativeProduct m n a r) t := by
  rw [iteratedDeriv_eq_alternatingPairJet
    (fun m n => thetaCuspCenterMixedDerivativeProductIntegral m n a)
    (fun m n t => hasDerivAt_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha m n t)]
  have hjet (r : ℝ) := iteratedDeriv_eq_alternatingPairJet
    (fun m n => thetaCuspCenterMixedDerivativeProduct m n a r)
    (fun m n t => hasDerivAt_thetaCuspCenterMixedDerivativeProduct m n a r t) k m n
  simp_rw [hjet]
  exact (integral_alternatingPairJet
    (fun m n r => thetaCuspCenterMixedDerivativeProduct m n a r t)
    (fun m n => integrable_thetaCuspCenterMixedDerivativeProduct ha0 ha m n) k m n).symm

/-- At difference zero the weighted derivative is the literal native reflection jet. -/
theorem iteratedDeriv_thetaCuspCenterMixedDerivativeProduct_zero_zero
    (k : ℕ) (a r : ℝ) :
    iteratedDeriv k (thetaCuspCenterMixedDerivativeProduct 0 0 a r) 0 =
      r*Real.sinh (a*r)*thetaCuspNativeReflectionJet k (r/2) := by
  unfold thetaCuspCenterMixedDerivativeProduct
  simp only [iteratedDeriv_zero]
  rw [iteratedDeriv_const_mul_field]
  rfl

/-- Every weighted native reflection jet is integrable at critical apertures. -/
theorem integrableOn_thetaCuspWeightedNativeReflectionJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (k : ℕ) :
    IntegrableOn (fun r : ℝ => r*Real.sinh (a*r)*thetaCuspNativeReflectionJet k (r/2)) (Ioi 0) := by
  simpa only [iteratedDeriv_thetaCuspCenterMixedDerivativeProduct_zero_zero] using
    integrable_iteratedDeriv_thetaCuspCenterMixedDerivativeProduct ha0 ha k 0 0 0

/-- The complete literal center-mixed jet is the center integral of the native jets. -/
theorem iteratedDeriv_thetaCuspCenterMixedDensity_eq_integral_nativeJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (k : ℕ) :
    iteratedDeriv k (thetaCuspCenterMixedDensity a) 0 =
      ∫ r : ℝ in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeReflectionJet k (r/2) := by
  change iteratedDeriv k (thetaCuspCenterMixedDerivativeProductIntegral 0 0 a) 0 = _
  rw [iteratedDeriv_thetaCuspCenterMixedDerivativeProductIntegral ha0 ha,
    show (fun r : ℝ => iteratedDeriv k (thetaCuspCenterMixedDerivativeProduct 0 0 a r) 0) =
      (fun r => r*Real.sinh (a*r)*thetaCuspNativeReflectionJet k (r/2)) from
      funext (iteratedDeriv_thetaCuspCenterMixedDerivativeProduct_zero_zero k a)]

/-- Fourier-signed native reflection jet, before center integration. -/
def thetaCuspNativeSignedJet (x : ℝ) (k : ℕ) : ℝ :=
  ((-Complex.I)^k).re * thetaCuspNativeReflectionJet k x

/-- Signed source jets preserve the literal center integration exactly. -/
theorem thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (k : ℕ) :
    thetaCuspCenterMixedSignedJet a k =
      ∫ r : ℝ in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSignedJet (r/2) k := by
  unfold thetaCuspCenterMixedSignedJet thetaCuspNativeSignedJet
  rw [iteratedDeriv_thetaCuspCenterMixedDensity_eq_integral_nativeJet ha0 ha,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  ring

/-- Every weighted Fourier-signed native jet is integrable. -/
theorem integrableOn_thetaCuspWeightedNativeSignedJet
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) (k : ℕ) :
    IntegrableOn (fun r : ℝ => r*Real.sinh (a*r)*thetaCuspNativeSignedJet (r/2) k) (Ioi 0) := by
  exact ((integrableOn_thetaCuspWeightedNativeReflectionJet ha0 ha k).const_mul
    (((-Complex.I)^k).re)).congr (ae_of_all _ fun r => by
      unfold thetaCuspNativeSignedJet
      ring)

/-- The finite native signed Hankel form tested before center integration. -/
def thetaCuspNativeSignedHankelForm {N : ℕ} (x : ℝ) (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, v i*v j*thetaCuspNativeSignedJet x (i.val+j.val)

/-- Every weighted native finite Hankel form is integrable. -/
theorem integrableOn_thetaCuspWeightedNativeSignedHankelForm
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) {N : ℕ} (v : Fin N → ℝ) :
    IntegrableOn (fun r : ℝ => r*Real.sinh (a*r)*thetaCuspNativeSignedHankelForm (r/2) v)
      (Ioi 0) := by
  have hi (i j : Fin N) := (integrableOn_thetaCuspWeightedNativeSignedJet ha0 ha (i.val+j.val)).const_mul
    (v i*v j)
  have hsum := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))
  apply hsum.congr
  filter_upwards with r
  simp only [thetaCuspNativeSignedHankelForm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every finite signed center-mixed Hankel form is the integral of the literal native form. -/
theorem thetaCuspCenterMixedSignedHankelForm_eq_integral_native
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) {N : ℕ} (v : Fin N → ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, v i*v j*thetaCuspCenterMixedSignedJet a (i.val+j.val)) =
      ∫ r : ℝ in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSignedHankelForm (r/2) v := by
  have hi (i j : Fin N) := (integrableOn_thetaCuspWeightedNativeSignedJet ha0 ha (i.val+j.val)).const_mul
    (v i*v j)
  have hpoint (r : ℝ) : r*Real.sinh (a*r)*thetaCuspNativeSignedHankelForm (r/2) v =
      ∑ i : Fin N, ∑ j : Fin N,
        (v i*v j)*(r*Real.sinh (a*r)*thetaCuspNativeSignedJet (r/2) (i.val+j.val)) := by
    simp only [thetaCuspNativeSignedHankelForm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet ha0 ha]

/-- Complete integrated native source cone; pointwise fibre positivity is not required. -/
def ThetaCuspIntegratedNativeSignedCone : Prop :=
  ∀ a : ℝ, 0 < a → a < 1/2 → ∀ (N : ℕ) (v : Fin N → ℝ),
    0 ≤ ∫ r : ℝ in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSignedHankelForm (r/2) v

/-- The all-order integrated native source comparison is exactly RH. -/
theorem thetaCuspIntegratedNativeSignedCone_iff_riemannHypothesis :
    ThetaCuspIntegratedNativeSignedCone ↔ RiemannHypothesis := by
  rw [← thetaCuspCenterMixedSignedJetCone_iff_riemannHypothesis]
  constructor
  · intro h a ha0 ha N v
    rw [thetaCuspCenterMixedSignedHankelForm_eq_integral_native ha0.le ha]
    exact h a ha0 ha N v
  · intro h a ha0 ha N v
    rw [← thetaCuspCenterMixedSignedHankelForm_eq_integral_native ha0.le ha]
    exact h a ha0 ha N v

end
end RHTower
