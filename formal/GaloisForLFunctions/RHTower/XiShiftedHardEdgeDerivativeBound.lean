import GaloisForLFunctions.RHTower.XiShiftedHardEdgeAngularMomentum
import GaloisForLFunctions.HTGeometry.RealTrigDegree

/-!
# The iterated spectral derivative of the rational hard-edge test

Through the Cayley half-density the derivative in the spectral variable acts on the angular profile
as

`T F = (1/a)·(-(1/2)·sin θ·F + (1 + cos θ)·F')`,

because `sin θ = 2 sin(θ/2) cos(θ/2)`, `1 + cos θ = 2 cos²(θ/2)` and `cos²(ψ(x)/2) = a²/(a²+x²)`.
Iterating the trigonometric bound for `T` and transporting back through the Cayley isometry gives

`∫ (d/dx)^m g_{a,p}² ≤ (∏_{i<m} (1/a)(1/2 + 2(N+i)))²·∫ g_{a,p}²`,

whose right-hand side tends to `(2C)^{2m}` along a family with `N ≤ Ca` and `a → ∞`.  This is the
plain-derivative form of the angular-momentum bound, the one Plancherel converts into a
Paley–Wiener support statement.
-/

open Set MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## Cosine polynomials have bounded degree -/

theorem realTrigDeg_cosPoly (N : ℕ) (b : ℕ → ℝ) : RealTrigDeg N (cosPoly N b) := by
  have hterm : ∀ j ∈ Finset.range (N + 1),
      RealTrigDeg N (fun θ => b j * Real.cos ((j : ℝ) * θ)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    exact RealTrigDeg.mono (by omega) ((realTrigDeg_cos_natMul j).smul (b j))
  refine (RealTrigDeg.sum (Finset.range (N + 1))
    (fun j => fun θ => b j * Real.cos ((j : ℝ) * θ)) hterm).congr fun θ => ?_
  rw [cosPoly]

/-! ## The Cayley transport is the spectral derivative -/

theorem cos_half_inverseChart_sq {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Real.cos (routeUHardEdgeInverseChart a x / 2) ^ 2 = a ^ 2 / (a ^ 2 + x ^ 2) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hpos : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  rw [routeUHardEdgeInverseChart_half, Real.cos_arctan]
  have hsqrt : Real.sqrt (1 + (x / a) ^ 2) ^ 2 = 1 + (x / a) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hne : Real.sqrt (1 + (x / a) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (1 + (x / a) ^ 2) := Real.sqrt_pos.mpr (by positivity)
    exact ne_of_gt this
  rw [div_pow, one_pow, hsqrt]
  field_simp

theorem hasDerivAt_routeUCayleyLift_step {a : ℝ} (ha : 0 < a) {F F' : ℝ → ℝ}
    (hF : ∀ θ : ℝ, HasDerivAt F (F' θ) θ) (x : ℝ) :
    HasDerivAt (routeUCayleyLift a F) (routeUCayleyLift a (trigCayleyStep a F F') x) x := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hpos : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  have hbase := hasDerivAt_routeUCayleyLift ha hF x
  refine hbase.congr_deriv ?_
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ, ψ = routeUHardEdgeInverseChart a x := ⟨_, rfl⟩
  rw [routeUCayleyLift, trigCayleyStep, ← hψ]
  have hsin : Real.sin ψ = 2 * Real.sin (ψ / 2) * Real.cos (ψ / 2) := by
    rw [show ψ = 2 * (ψ / 2) by ring, Real.sin_two_mul]
    ring_nf
  have hcos : 1 + Real.cos ψ = 2 * Real.cos (ψ / 2) ^ 2 := by
    rw [show ψ = 2 * (ψ / 2) by ring, Real.cos_two_mul]
    ring_nf
  have hsq : Real.cos (ψ / 2) ^ 2 = a ^ 2 / (a ^ 2 + x ^ 2) := by
    rw [hψ]
    exact cos_half_inverseChart_sq ha x
  rw [hsin, hcos]
  have hexpand : Real.cos (ψ / 2)
      * (1 / a * (-(1 / 2) * (2 * Real.sin (ψ / 2) * Real.cos (ψ / 2)) * F ψ
        + 2 * Real.cos (ψ / 2) ^ 2 * F' ψ))
      = (2 / a) * Real.cos (ψ / 2) ^ 2
        * (-(1 / 2) * Real.sin (ψ / 2) * F ψ + Real.cos (ψ / 2) * F' ψ) := by
    field_simp
  rw [hexpand, hsq]
  have hfac : (2 / a) * (a ^ 2 / (a ^ 2 + x ^ 2)) = 2 * a / (a ^ 2 + x ^ 2) := by
    field_simp
  rw [hfac]

/-! ## The iterated derivative -/

theorem iteratedDeriv_routeUCayleyLift {a : ℝ} (ha : 0 < a) {D : ℕ} :
    ∀ (m : ℕ) {F : ℝ → ℝ}, RealTrigDeg D F →
      iteratedDeriv m (routeUCayleyLift a F) = routeUCayleyLift a (trigCayleyIter a m F) := by
  intro m
  induction m with
  | zero =>
    intro F _
    rw [iteratedDeriv_zero, trigCayleyIter_zero]
  | succ m ih =>
    intro F hF
    have hiter : RealTrigDeg (D + m) (trigCayleyIter a m F) :=
      realTrigDeg_trigCayleyIter m D hF
    rw [iteratedDeriv_succ, ih hF]
    funext x
    have hstep := hasDerivAt_routeUCayleyLift_step ha
      (F := trigCayleyIter a m F) (F' := deriv (trigCayleyIter a m F))
      (fun θ => hiter.hasDerivAt θ) x
    rw [hstep.deriv, trigCayleyIter_succ]

/-- **The iterated spectral derivative bound for a Cayley lift.** -/
theorem integral_iteratedDeriv_routeUCayleyLift_sq_le {a : ℝ} (ha : 0 < a) {D : ℕ} (m : ℕ)
    {F : ℝ → ℝ} (hF : RealTrigDeg D F) :
    (∫ x : ℝ, iteratedDeriv m (routeUCayleyLift a F) x ^ 2)
      ≤ (∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ)))) ^ 2
          * ∫ x : ℝ, routeUCayleyLift a F x ^ 2 := by
  have hbound := trigNorm_trigCayleyIter_le ha m D hF
  have hP : (0 : ℝ) ≤ ∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ))) := by
    refine Finset.prod_nonneg fun i _ => ?_
    have h1 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have h3 : (0 : ℝ) < 1 / a := by positivity
    nlinarith
  have hsq : trigNorm (trigCayleyIter a m F) ^ 2
      ≤ (∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ)))) ^ 2
        * trigNorm F ^ 2 := by
    have hn : (0 : ℝ) ≤ trigNorm (trigCayleyIter a m F) := trigNorm_nonneg _
    have hn2 : (0 : ℝ) ≤ trigNorm F := trigNorm_nonneg F
    nlinarith [hbound, hP, hn, hn2]
  rw [iteratedDeriv_routeUCayleyLift ha m hF, integral_routeUCayleyLift_sq ha,
    integral_routeUCayleyLift_sq ha, integral_Ioo_eq_intervalIntegral,
    integral_Ioo_eq_intervalIntegral, ← trigNorm_sq, ← trigNorm_sq]
  have ha2 : (0 : ℝ) ≤ a / 2 := by positivity
  nlinarith [hsq, ha2]

end RHTower

end
