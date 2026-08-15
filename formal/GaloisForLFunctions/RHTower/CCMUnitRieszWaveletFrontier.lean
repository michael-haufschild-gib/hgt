import GaloisForLFunctions.RHTower.CCMUnitRieszQuadratureDefect

/-!
# The unit-Riesz Möbius wavelet: compensation, renewal, and the pole-channel margin

Six exact mechanisms of the card are formalized, on top of the layer-cake quadrature defect already
proved in `CCMUnitRieszQuadratureDefect`.

*The progression mass.*  `K_N(q) = 2√N/(3q) − 2 η(N/q)/√N`, equation `(7)`: every individual
modulus has a sharp `O(N^{-1/2})` quadrature defect.

*The exact Möbius compensation.*  `P_N − N/3 = (N/3)(Q_N − 1) + ∑_q μ(q)log q · η(N/q)`, equation
`(10)`: the two main parts cancel exactly, so they may not be bounded separately.

*The renewal normalization.*  `J_N = (2√N/3)(S_N − 1)`, equation `(15)`.

*The zero-mean wavelet.*  `∫_0^T K_T = 0`, equation `(18)`, from the vanishing of `Φ_T` at both
endpoints.

*The pole-channel margin.*  `∫_0^T u e^{-u} du = 1 − (T+1)e^{-T}` exactly, and with the sharp
cutoff bound `1 − W(t) ≤ 3/t` this gives `1 − A_T ≤ (3T²/2 + T + 1)e^{-T}`, equations
`(20)`–`(22)`.

*The frontier identity.*  `S_N − 1 = (A_T − 1) − ∫_0^T h_0 K_T`, equation `(23)`.

The Möbius divisor law `(9)`, the Stieltjes partial summation producing `(18)`, and the causal
graph identity `(19)` are cited parents and stay outside the Lean statement.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The progression mass -/

/-- The averaged CCM prime weight on multiples of `q`, equation `(7)`. -/
def progressionMass (N q : ℝ) : ℝ := 2 / Real.sqrt N * rieszProgressionSum (N / q)

/-- **Equation (7).**  Every modulus has a sharp `O(N^{-1/2})` quadrature defect. -/
theorem progressionMass_eq {N q : ℝ} (hN : 0 < N) :
    progressionMass N q
      = 2 * Real.sqrt N / (3 * q) - 2 / Real.sqrt N * rieszQuadratureDefect (N / q) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (le_of_lt hN)
  have hg : rieszProgressionSum (N / q) = (N / q) / 3 - rieszQuadratureDefect (N / q) := by
    rw [rieszQuadratureDefect]
    ring
  rw [progressionMass, hg]
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · field_simp
    nlinarith [hsq]

/-! ## The exact Möbius compensation -/

/-- **Equation (10).**  The polar main term and the Möbius main term cancel exactly, leaving only
the quadrature defect. -/
theorem mobius_compensation {ι : Type*} (Q : Finset ι) (mu lg qq : ι → ℝ) (N : ℝ) :
    (-∑ q ∈ Q, mu q * lg q * rieszProgressionSum (N / qq q)) - N / 3
      = N / 3 * ((-∑ q ∈ Q, mu q * lg q / qq q) - 1)
        + ∑ q ∈ Q, mu q * lg q * rieszQuadratureDefect (N / qq q) := by
  have hsplit : ∀ q : ι, mu q * lg q * rieszProgressionSum (N / qq q)
      = N / 3 * (mu q * lg q / qq q) - mu q * lg q * rieszQuadratureDefect (N / qq q) := by
    intro q
    rw [rieszQuadratureDefect]
    rcases eq_or_ne (qq q) 0 with hq | hq
    · rw [hq]
      simp
    · field_simp
      ring
  rw [Finset.sum_congr rfl fun q _ => hsplit q]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-! ## The renewal normalization -/

/-- **Equation (15).**  The normalized Riesz mass is the renewal excess. -/
theorem riesz_normalization_eq {N P S J : ℝ} (hN : 0 < N)
    (hS : S = 3 * P / N) (hJ : J = 2 / Real.sqrt N * (P - N / 3)) :
    J = 2 * Real.sqrt N / 3 * (S - 1) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (le_of_lt hN)
  rw [hJ, hS]
  field_simp
  rw [Real.sq_sqrt (le_of_lt hN)]

/-! ## The zero-mean wavelet -/

/-- **Equation (18), zero mean.**  The wavelet kernel has vanishing total mass because its
primitive vanishes at both endpoints. -/
theorem integral_kernel_zero_mean {Phi K : ℝ → ℝ} {T : ℝ}
    (hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) T, HasDerivAt Phi (K u) u)
    (hint : IntervalIntegrable K volume 0 T)
    (h0 : Phi 0 = 0) (hTend : Phi T = 0) :
    (∫ u in (0 : ℝ)..T, K u) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, h0, hTend, sub_zero]

/-! ## The pole-channel margin -/

/-- The exact first moment of the exponential on a finite window. -/
theorem integral_u_exp_neg {T : ℝ} :
    (∫ u in (0 : ℝ)..T, u * Real.exp (-u)) = 1 - (T + 1) * Real.exp (-T) := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => -((s + 1) * Real.exp (-s))) (u * Real.exp (-u)) u := by
    intro u _
    have hA : HasDerivAt (fun s : ℝ => s + 1) 1 u := by
      simpa using (hasDerivAt_id u).add_const 1
    have hneg : HasDerivAt (fun s : ℝ => -s) (-1) u := by
      simpa using (hasDerivAt_id u).fun_neg
    have hB : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-u)) u := by
      simpa using hneg.exp
    have hAB := hA.fun_mul hB
    have hres := hAB.fun_neg
    refine hres.congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun u : ℝ => u * Real.exp (-u)) (Set.uIcc 0 T) := by
    fun_prop
  have hval : -((T + 1) * Real.exp (-T)) - -((0 + 1) * Real.exp (-0))
      = 1 - (T + 1) * Real.exp (-T) := by
    rw [neg_zero, Real.exp_zero]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable, hval]

/-- **Equations (20)–(22).**  With the sharp cutoff bound the pole channel is saturated at `1` with
an explicit exponential margin. -/
theorem one_sub_poleChannel_le {T : ℝ} (hT : 0 ≤ T) {W : ℝ → ℝ}
    (hWtail : ∀ u : ℝ, 0 ≤ u → u ≤ T →
      u * Real.exp (-u) * (1 - W (Real.exp (T - u))) ≤ 3 * u * Real.exp (-T))
    (hcont : ContinuousOn (fun u : ℝ => u * Real.exp (-u) * W (Real.exp (T - u)))
      (Set.uIcc 0 T)) :
    1 - (∫ u in (0 : ℝ)..T, u * Real.exp (-u) * W (Real.exp (T - u)))
      ≤ (3 * T ^ 2 / 2 + T + 1) * Real.exp (-T) := by
  have hcont0 : ContinuousOn (fun u : ℝ => u * Real.exp (-u)) (Set.uIcc 0 T) := by fun_prop
  have hcontd : ContinuousOn
      (fun u : ℝ => u * Real.exp (-u) * (1 - W (Real.exp (T - u)))) (Set.uIcc 0 T) := by
    have hsub : (fun u : ℝ => u * Real.exp (-u) * (1 - W (Real.exp (T - u))))
        = fun u : ℝ => u * Real.exp (-u) - u * Real.exp (-u) * W (Real.exp (T - u)) := by
      funext u
      ring
    rw [hsub]
    exact hcont0.sub hcont
  have hcontr : ContinuousOn (fun u : ℝ => 3 * u * Real.exp (-T)) (Set.uIcc 0 T) := by fun_prop
  have hmono : (∫ u in (0 : ℝ)..T, u * Real.exp (-u) * (1 - W (Real.exp (T - u))))
      ≤ ∫ u in (0 : ℝ)..T, 3 * u * Real.exp (-T) := by
    refine intervalIntegral.integral_mono_on hT hcontd.intervalIntegrable
      hcontr.intervalIntegrable ?_
    intro u hu
    exact hWtail u hu.1 hu.2
  have hright : (∫ u in (0 : ℝ)..T, 3 * u * Real.exp (-T)) = 3 * Real.exp (-T) * (T ^ 2 / 2) := by
    have hrw : (fun u : ℝ => 3 * u * Real.exp (-T))
        = fun u : ℝ => (3 * Real.exp (-T)) * u := by
      funext u
      ring
    rw [hrw, intervalIntegral.integral_const_mul, integral_id]
    simp
  have hsplit : (∫ u in (0 : ℝ)..T, u * Real.exp (-u) * (1 - W (Real.exp (T - u))))
      = (∫ u in (0 : ℝ)..T, u * Real.exp (-u))
        - ∫ u in (0 : ℝ)..T, u * Real.exp (-u) * W (Real.exp (T - u)) := by
    rw [← intervalIntegral.integral_sub hcont0.intervalIntegrable hcont.intervalIntegrable]
    refine intervalIntegral.integral_congr fun u _ => ?_
    ring
  rw [hsplit, integral_u_exp_neg] at hmono
  rw [hright] at hmono
  linarith

/-! ## The frontier identity -/

/-- **Equation (23).**  The renewal excess is the pole-channel margin minus one signed
causal-complement wavelet coefficient. -/
theorem frontier_identity {m h K : ℝ → ℝ} {T S A : ℝ}
    (hm : ∀ u, m u = Real.exp (-u) - h u)
    (hS : S = ∫ u in (0 : ℝ)..T, m u * K u)
    (hA : A = ∫ u in (0 : ℝ)..T, Real.exp (-u) * K u)
    (hint1 : IntervalIntegrable (fun u => Real.exp (-u) * K u) volume 0 T)
    (hint2 : IntervalIntegrable (fun u => h u * K u) volume 0 T) :
    S - 1 = (A - 1) - ∫ u in (0 : ℝ)..T, h u * K u := by
  have hrw : (∫ u in (0 : ℝ)..T, m u * K u)
      = (∫ u in (0 : ℝ)..T, Real.exp (-u) * K u) - ∫ u in (0 : ℝ)..T, h u * K u := by
    rw [← intervalIntegral.integral_sub hint1 hint2]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [hm u]
    ring
  rw [hS, hrw, hA]
  ring


/-- **Equation (25).**  The one-sided CCM bound on the normalized Riesz mass is *equivalent* to a
one-sided lower bound on the single causal-complement wavelet coefficient, with the pole-channel
margin `A_T − 1` as the only other term. -/
theorem frontier_equivalence {N M A S J X : ℝ} (hN : 0 < N)
    (hJ : J = 2 * Real.sqrt N / 3 * (S - 1))
    (hfront : S - 1 = (A - 1) - X) :
    J ≤ M ↔ (A - 1) - 3 * M / (2 * Real.sqrt N) ≤ X := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hcoef : 0 < 2 * Real.sqrt N / 3 := by positivity
  rw [hJ, hfront]
  constructor
  · intro hle
    have hdiv : (A - 1) - X ≤ M / (2 * Real.sqrt N / 3) := by
      rw [le_div_iff₀ hcoef]
      linarith [hle]
    have hval : M / (2 * Real.sqrt N / 3) = 3 * M / (2 * Real.sqrt N) := by
      field_simp
    rw [hval] at hdiv
    linarith
  · intro hge
    have hdiv : (A - 1) - X ≤ 3 * M / (2 * Real.sqrt N) := by linarith
    have hval : 3 * M / (2 * Real.sqrt N) = M / (2 * Real.sqrt N / 3) := by
      field_simp
    rw [hval] at hdiv
    calc 2 * Real.sqrt N / 3 * ((A - 1) - X)
        = ((A - 1) - X) * (2 * Real.sqrt N / 3) := by ring
      _ ≤ M := (le_div_iff₀ hcoef).mp hdiv

end GaloisForLFunctions.RHTower

end
