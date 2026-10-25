import GaloisForLFunctions.MultiplicativePositivityGeometry.ArithmeticRealization
import GaloisForLFunctions.MultiplicativePositivityGeometry.ProgressionModels

/-!
# The calculus of boundary data

Boundary data form a cone with three operations, and the boundary divisor is linear in them:

* **scaling** `c · w`, divisor `c · D`: the power `Z^c` (`IsBoundaryDivisor.smul`);
* **sum** over a disjoint union of index types, divisors add: the product of two Euler products
  (`IsBoundaryDivisor.sum`);
* **twist** by a nonnegative cosine polynomial `P(t₀ λ)`, divisor
  `Σ_k (a_k/2)(D(u + kt₀) + D(u − kt₀))`: the product `Π_k (Z(s+ikt₀) Z(s−ikt₀))^{a_k/2}`
  (`IsBoundaryDivisor.twist`).

Data whose total mass stays bounded at the boundary contribute nothing
(`isBoundaryDivisor_zero_of_bounded`). Hence the boundary divisor cannot see the interior. The
product of `ζ(s)` and the alternating one-prime factor `Φ(s + κ)` has nonnegative weights and
`D = 1_{0}`, so it satisfies all four boundary invariants, yet it vanishes at `1 − κ + iπ/ℓ`
inside the strip (`interior_zero_invisible`). The factor pays with interior poles at
`1 − κ + 2πik/ℓ`. On the boundary, multiplicative positivity separates nothing in the interior.
-/

open Filter Topology Finset Complex

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

variable {ι ι' : Type*} {lam : ι → ℝ} {w : ℝ → ι → ℝ} {D : ℝ → ℝ}

/-- **Scaling.** -/
theorem IsBoundaryDivisor.smul (hD : IsBoundaryDivisor lam w D) {c : ℝ} (hc : 0 ≤ c) :
    IsBoundaryDivisor lam (fun x i => c * w x i) (fun u => c * D u) where
  nonneg x hx i := mul_nonneg hc (hD.nonneg x hx i)
  summable x hx := (hD.summable x hx).mul_left c
  tendsto u := by
    refine ((hD.tendsto u).const_mul c).congr' (Eventually.of_forall fun x => ?_)
    simp only [cosineTrace, mul_assoc, tsum_mul_left]
    ring

/-- **Sum: Euler products multiply, divisors add.** -/
theorem IsBoundaryDivisor.sum {lam' : ι' → ℝ} {w' : ℝ → ι' → ℝ} {D' : ℝ → ℝ}
    (hD : IsBoundaryDivisor lam w D) (hD' : IsBoundaryDivisor lam' w' D') :
    IsBoundaryDivisor (Sum.elim lam lam') (fun x => Sum.elim (w x) (w' x))
      (fun u => D u + D' u) where
  nonneg x hx i := by
    cases i with
    | inl i => exact hD.nonneg x hx i
    | inr i => exact hD'.nonneg x hx i
  summable x hx := Summable.sum _ (hD.summable x hx) (hD'.summable x hx)
  tendsto u := by
    refine ((hD.tendsto u).add (hD'.tendsto u)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have h1 := summable_cosineTrace_terms (hD.nonneg x hx) (hD.summable x hx) lam u
    have h2 := summable_cosineTrace_terms (hD'.nonneg x hx) (hD'.summable x hx) lam' u
    unfold cosineTrace
    rw [Summable.tsum_sum (f := fun i => Sum.elim (w x) (w' x) i *
      Real.cos (Sum.elim lam lam' i * u)) h1 h2]
    simp only [Sum.elim_inl, Sum.elim_inr]
    ring

/-- Weights twisted by the cosine polynomial `P(t₀ λ_i)`. -/
noncomputable def twistWeight (lam : ι → ℝ) (w : ℝ → ι → ℝ) (a : ℕ → ℝ) (K : ℕ) (t₀ x : ℝ)
    (i : ι) : ℝ :=
  w x i * HTGeometry.cosinePolynomial a K (t₀ * lam i)

/-- The twisted divisor `Σ_k (a_k/2)(D(u + kt₀) + D(u − kt₀))`. -/
noncomputable def twistDivisor (D : ℝ → ℝ) (a : ℕ → ℝ) (K : ℕ) (t₀ u : ℝ) : ℝ :=
  ∑ k ∈ range (K + 1), a k / 2 * (D (u + k * t₀) + D (u - k * t₀))

/-- **Twist.** Twisting a boundary datum by a nonnegative cosine polynomial shifts and averages
its divisor. -/
theorem IsBoundaryDivisor.twist (hD : IsBoundaryDivisor lam w D) {a : ℕ → ℝ} {K : ℕ}
    (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ) (t₀ : ℝ) :
    IsBoundaryDivisor lam (twistWeight lam w a K t₀) (twistDivisor D a K t₀) where
  nonneg x hx i := mul_nonneg (hD.nonneg x hx i) (hP _)
  summable x hx := Summable.of_nonneg_of_le (fun i => mul_nonneg (hD.nonneg x hx i) (hP _))
    (fun i => mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (abs_cosinePolynomial_le a K _)) (hD.nonneg x hx i))
    ((hD.summable x hx).mul_right _)
  tendsto u := by
    have hlim : Tendsto (fun x => ∑ k ∈ range (K + 1), a k / 2 *
          (x * cosineTrace (w x) lam (u + k * t₀) + x * cosineTrace (w x) lam (u - k * t₀)))
        (𝓝[>] 0) (𝓝 (twistDivisor D a K t₀ u)) :=
      tendsto_finsetSum _ fun k _ => ((hD.tendsto _).add (hD.tendsto _)).const_mul _
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hnn := hD.nonneg x hx
    have hs := hD.summable x hx
    have hS : HasSum (fun i => ∑ k ∈ range (K + 1), a k / 2 *
          (w x i * Real.cos (lam i * (u + k * t₀)) + w x i * Real.cos (lam i * (u - k * t₀))))
        (∑ k ∈ range (K + 1), a k / 2 *
          (cosineTrace (w x) lam (u + k * t₀) + cosineTrace (w x) lam (u - k * t₀))) :=
      hasSum_sum fun k _ => (((summable_cosineTrace_terms hnn hs lam _).hasSum).add
        ((summable_cosineTrace_terms hnn hs lam _).hasSum)).mul_left _
    have htrace : cosineTrace (twistWeight lam w a K t₀ x) lam u =
        ∑ k ∈ range (K + 1), a k / 2 *
          (cosineTrace (w x) lam (u + k * t₀) + cosineTrace (w x) lam (u - k * t₀)) := by
      rw [← hS.tsum_eq]
      unfold cosineTrace
      refine tsum_congr fun i => ?_
      unfold twistWeight HTGeometry.cosinePolynomial
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => twist_mode _ _ _ _ _ _
    rw [htrace, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- **Bounded data are invisible.** Nonnegative weights whose total mass stays bounded as `x ↓ 0`
have boundary divisor `0`. -/
theorem isBoundaryDivisor_zero_of_bounded (hnn : ∀ x, 0 < x → ∀ i, 0 ≤ w x i)
    (hs : ∀ x, 0 < x → Summable (w x)) {C : ℝ}
    (hC : ∀ x, 0 < x → x ≤ 1 → ∑' i, w x i ≤ C) : IsBoundaryDivisor lam w (fun _ => 0) where
  nonneg := hnn
  summable := hs
  tendsto u := by
    have htr : ∀ x, 0 < x → |cosineTrace (w x) lam u| ≤ ∑' i, w x i := fun x hx => by
      have h1 := summable_cosineTrace_terms (hnn x hx) (hs x hx) lam u
      refine abs_le.mpr ⟨?_, ?_⟩
      · rw [← tsum_neg]
        exact Summable.tsum_le_tsum (fun i => by
          nlinarith [Real.neg_one_le_cos (lam i * u), hnn x hx i]) (hs x hx).neg h1
      · exact Summable.tsum_le_tsum (fun i => mul_le_of_le_one_right (hnn x hx i)
          (Real.cos_le_one _)) h1 (hs x hx)
    have hlin : Tendsto (fun x : ℝ => x * C) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const C).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlin
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx.1]
    exact mul_le_mul_of_nonneg_left ((htr x hx.1).trans (hC x hx.1 hx.2)) hx.1.le

/-- A progression datum pushed into the interior by `κ > 0` is invisible on the boundary. -/
theorem shifted_progression_invisible {h c κ : ℝ} (hh : 0 < h) (hc : 0 ≤ c) (hκ : 0 < κ) :
    IsBoundaryDivisor (progressionFrequency h c) (fun x => progressionWeight h c (x + κ))
      (fun _ => 0) := by
  have hden : 0 < 1 - Real.exp (-(h * κ)) := by
    have : Real.exp (-(h * κ)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
    linarith
  refine isBoundaryDivisor_zero_of_bounded (fun x hx => progressionWeight_nonneg hh _)
    (fun x hx => (hasSum_progressionWeight hh (by linarith)).summable)
    (C := h * (1 - Real.exp (-(h * κ)))⁻¹) fun x hx _ => ?_
  have hxκ : 0 < x + κ := by linarith
  rw [(hasSum_progressionWeight (c := c) hh hxκ).tsum_eq]
  have he : Real.exp (-(c * (x + κ))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hmono : Real.exp (-(h * (x + κ))) ≤ Real.exp (-(h * κ)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hinv : (1 - Real.exp (-(h * (x + κ))))⁻¹ ≤ (1 - Real.exp (-(h * κ)))⁻¹ :=
    inv_anti₀ hden (by linarith)
  have hinv0 : 0 ≤ (1 - Real.exp (-(h * (x + κ))))⁻¹ := inv_nonneg.mpr (by linarith)
  calc h * Real.exp (-(c * (x + κ))) * (1 - Real.exp (-(h * (x + κ))))⁻¹
      ≤ h * 1 * (1 - Real.exp (-(h * (x + κ))))⁻¹ := by gcongr
    _ ≤ h * (1 - Real.exp (-(h * κ)))⁻¹ := by rw [mul_one]; gcongr

/-- On `Re s = 1 + x`, the cosine trace of the shifted alternating datum is
`Re(−Φ'/Φ)(s + κ)` for the corpus one-prime factor `Φ = periodicPoleZeta ℓ`. -/
theorem periodicPole_shifted_trace {ℓ κ x : ℝ} (hℓ : 0 < ℓ) (hxκ : 0 < x + κ) (u : ℝ) :
    (ArithmeticCastelnuovoSeveri.periodicPoleNegLogDeriv ℓ
        (((1 + (x + κ) : ℝ) : ℂ) + (u : ℂ) * I)).re =
      cosineTrace (progressionWeight (2 * ℓ) ℓ (x + κ)) (progressionFrequency (2 * ℓ) ℓ) u := by
  rw [progression_trace_eq (by linarith) hxκ u]
  unfold ArithmeticCastelnuovoSeveri.periodicPoleNegLogDeriv progressionKernel
  have e1 : -(((((1 + (x + κ) : ℝ) : ℂ) + (u : ℂ) * I) - 1) * (ℓ : ℂ)) =
      -(ℓ : ℂ) * (((x + κ : ℝ) : ℂ) + (u : ℂ) * I) := by push_cast; ring
  have e2 : Complex.exp (-(ℓ : ℂ) * (((x + κ : ℝ) : ℂ) + (u : ℂ) * I)) ^ 2 =
      Complex.exp (-((2 * ℓ : ℝ) : ℂ) * (((x + κ : ℝ) : ℂ) + (u : ℂ) * I)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e1, e2, show (2 : ℂ) * (ℓ : ℂ) = ((2 * ℓ : ℝ) : ℂ) by push_cast; ring, mul_div_assoc,
    Complex.re_ofReal_mul]

/-- **Interior zeros are invisible on the boundary.** `ζ(s) · Φ(s + κ)` has nonnegative
weights and boundary divisor `1_{0}`, so it satisfies (N), (Z), (S) and (I). Its second factor is
the corpus one-prime function, and it vanishes at `1 − κ + iπ/ℓ`. -/
theorem interior_zero_invisible {ℓ κ : ℝ} (hℓ : 0 < ℓ) (hκ : 0 < κ) :
    IsBoundaryDivisor (Sum.elim logFrequency (progressionFrequency (2 * ℓ) ℓ))
      (fun x => Sum.elim (zetaBoundaryWeight x) (progressionWeight (2 * ℓ) ℓ (x + κ)))
      (fun u => if u = 0 then 1 else 0) ∧
    (∀ x u : ℝ, 0 < x →
      (ArithmeticCastelnuovoSeveri.periodicPoleNegLogDeriv ℓ
          (((1 + (x + κ) : ℝ) : ℂ) + (u : ℂ) * I)).re =
        cosineTrace (progressionWeight (2 * ℓ) ℓ (x + κ)) (progressionFrequency (2 * ℓ) ℓ) u) ∧
    ArithmeticCastelnuovoSeveri.periodicPoleZeta ℓ
      ((((1 - κ : ℝ) : ℂ) + ((Real.pi / ℓ : ℝ) : ℂ) * I) + (κ : ℂ)) = 0 := by
  refine ⟨?_, fun x u hx => periodicPole_shifted_trace hℓ (by linarith) u, ?_⟩
  · convert zeta_isBoundaryDivisor.sum
      (shifted_progression_invisible (by linarith : 0 < 2 * ℓ) hℓ.le hκ) using 1
    funext u
    rw [zetaBoundaryDivisor_eq, add_zero]
  · rw [show (((1 - κ : ℝ) : ℂ) + ((Real.pi / ℓ : ℝ) : ℂ) * I) + (κ : ℂ) =
        1 + ((Real.pi / ℓ : ℝ) : ℂ) * I by push_cast; ring]
    exact ArithmeticCastelnuovoSeveri.periodicPoleZeta_boundary_zero hℓ

end GaloisForLFunctions.MultiplicativePositivityGeometry
