import GaloisForLFunctions.HTGeometry.EnvelopeFromLogDerivative

/-!
# The scaled amplitude of a Sturm–Liouville solution

For a solution of `(p R')' + Q R = 0` and a scale `K > 0` set

```text
G = R² + (p R')² / K .
```

Then `G' = 2 R (p R') (1/p − Q/K)`, and the elementary inequality `2|R||p R'| ≤ sqrt K · G` turns any
bound `|1/p − Q/K| ≤ M` into the two-sided exponential envelope

```text
G(β) · exp(−M sqrt K (β − α))  ≤  G(α)  ≤  G(β) · exp(M sqrt K (β − α)) .
```

The point of the scale `K` is that it can be chosen to match the size of `Q`: on a window where `Q`
is comparable to `K` and `p` is comparable to `1`, the factor `M sqrt K` is of the order of the
local wavenumber, so the envelope costs only the accumulated phase.  Nothing here distinguishes the
oscillatory from the exponential regime — the estimate crosses a turning point without noticing it.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

/-- The Sturm amplitude at scale `K`: the solution squared plus the scaled flux squared. -/
def sturmAmplitude (p R DR : ℝ → ℝ) (K : ℝ) (y : ℝ) : ℝ := R y ^ 2 + (p y * DR y) ^ 2 / K

theorem sturmAmplitude_nonneg {p R DR : ℝ → ℝ} {K y : ℝ} (hK : 0 < K) :
    0 ≤ sturmAmplitude p R DR K y := by
  rw [sturmAmplitude]
  positivity

/-- The derivative of the scaled amplitude along a solution of `(p R')' + Q R = 0`. -/
theorem hasDerivAt_sturmAmplitude {p Q R DR : ℝ → ℝ} {K y : ℝ} (hK : K ≠ 0) (hp : p y ≠ 0)
    (hR : HasDerivAt R (DR y) y)
    (hflux : HasDerivAt (fun t => p t * DR t) (-(Q y * R y)) y) :
    HasDerivAt (sturmAmplitude p R DR K)
      (2 * R y * (p y * DR y) * (1 / p y - Q y / K)) y := by
  have h1 : HasDerivAt (fun t => R t ^ 2) (2 * R y * DR y) y := by
    have := hR.pow 2
    refine this.congr_deriv ?_
    ring
  have h2 : HasDerivAt (fun t => (p t * DR t) ^ 2 / K)
      (2 * (p y * DR y) * (-(Q y * R y)) / K) y := by
    have := (hflux.pow 2).div_const K
    refine this.congr_deriv ?_
    ring
  have h := h1.add h2
  refine h.congr_deriv ?_
  field_simp
  ring

/-- The cross term is dominated by the amplitude at the matching scale. -/
theorem abs_two_mul_le_sqrt_mul_sturmAmplitude {p R DR : ℝ → ℝ} {K y : ℝ} (hK : 0 < K) :
    |2 * R y * (p y * DR y)| ≤ Real.sqrt K * sturmAmplitude p R DR K y := by
  obtain ⟨S, hS0, hSK, hSeq⟩ : ∃ S : ℝ, 0 < S ∧ S * S = K ∧ Real.sqrt K = S :=
    ⟨Real.sqrt K, Real.sqrt_pos.2 hK, Real.mul_self_sqrt hK.le, rfl⟩
  rw [hSeq, sturmAmplitude, ← hSK]
  have hval : S * (R y ^ 2 + (p y * DR y) ^ 2 / (S * S))
      = (S ^ 2 * R y ^ 2 + (p y * DR y) ^ 2) / S := by
    field_simp
  rw [hval, abs_le]
  refine ⟨?_, ?_⟩
  · rw [neg_le, le_div_iff₀ hS0]
    nlinarith [sq_nonneg (S * R y + p y * DR y)]
  · rw [le_div_iff₀ hS0]
    nlinarith [sq_nonneg (S * R y - p y * DR y)]

section Envelope

variable {p Q R DR : ℝ → ℝ} {K M α β : ℝ}

/-- The amplitude is continuous wherever the solution and its flux are differentiable. -/
theorem continuousOn_sturmAmplitude
    (hR : ∀ y ∈ Icc α β, HasDerivAt R (DR y) y)
    (hflux : ∀ y ∈ Icc α β, HasDerivAt (fun t => p t * DR t) (-(Q y * R y)) y) :
    ContinuousOn (sturmAmplitude p R DR K) (Icc α β) := by
  have hRc : ContinuousOn R (Icc α β) := fun y hy => (hR y hy).continuousAt.continuousWithinAt
  have hFc : ContinuousOn (fun t => p t * DR t) (Icc α β) := fun y hy =>
    (hflux y hy).continuousAt.continuousWithinAt
  exact (hRc.pow 2).add ((hFc.pow 2).div_const K)

/-- **The scaled amplitude cannot grow backwards faster than the exponential envelope.** -/
theorem sturmAmplitude_le_mul_exp (hαβ : α ≤ β) (hK : 0 < K) (hM : 0 ≤ M)
    (hp : ∀ y ∈ Icc α β, p y ≠ 0)
    (hR : ∀ y ∈ Icc α β, HasDerivAt R (DR y) y)
    (hflux : ∀ y ∈ Icc α β, HasDerivAt (fun t => p t * DR t) (-(Q y * R y)) y)
    (hbound : ∀ y ∈ Icc α β, |1 / p y - Q y / K| ≤ M) :
    sturmAmplitude p R DR K α
      ≤ sturmAmplitude p R DR K β * Real.exp (M * Real.sqrt K * (β - α)) := by
  set G : ℝ → ℝ := sturmAmplitude p R DR K with hGdef
  set L : ℝ := M * Real.sqrt K with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    exact mul_nonneg hM (Real.sqrt_nonneg K)
  set F : ℝ → ℝ := fun y => G y * Real.exp (L * y) with hFdef
  set F' : ℝ → ℝ := fun y =>
    (2 * R y * (p y * DR y) * (1 / p y - Q y / K) + L * G y) * Real.exp (L * y) with hF'def
  have hGc : ContinuousOn G (Icc α β) := continuousOn_sturmAmplitude hR hflux
  have hFc : ContinuousOn F (Icc α β) :=
    hGc.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hFd : ∀ t ∈ Ioo α β, HasDerivAt F (F' t) t := by
    intro t ht
    have htI : t ∈ Icc α β := ⟨ht.1.le, ht.2.le⟩
    have hG := hasDerivAt_sturmAmplitude (K := K) (Q := Q) hK.ne' (hp t htI) (hR t htI)
      (hflux t htI)
    have hE : HasDerivAt (fun y : ℝ => Real.exp (L * y)) (Real.exp (L * t) * L) t := by
      have h1 : HasDerivAt (fun y : ℝ => L * y) L t := by
        simpa using (hasDerivAt_id t).const_mul L
      simpa using h1.exp
    have h := hG.mul hE
    refine h.congr_deriv ?_
    rw [hF'def]
    ring
  have hFnn : ∀ t ∈ Ioo α β, 0 ≤ F' t := by
    intro t ht
    have htI : t ∈ Icc α β := ⟨ht.1.le, ht.2.le⟩
    have hcross := abs_two_mul_le_sqrt_mul_sturmAmplitude (p := p) (R := R) (DR := DR)
      (K := K) (y := t) hK
    have hb := hbound t htI
    have hGnn : 0 ≤ G t := sturmAmplitude_nonneg (p := p) (R := R) (DR := DR) hK
    have hkey : |2 * R t * (p t * DR t) * (1 / p t - Q t / K)| ≤ L * G t := by
      rw [abs_mul, hLdef]
      calc |2 * R t * (p t * DR t)| * |1 / p t - Q t / K|
          ≤ (Real.sqrt K * G t) * M := by
            refine mul_le_mul hcross hb (abs_nonneg _) ?_
            exact mul_nonneg (Real.sqrt_nonneg K) hGnn
        _ = M * Real.sqrt K * G t := by ring
    have hlow : -(L * G t) ≤ 2 * R t * (p t * DR t) * (1 / p t - Q t / K) :=
      neg_le_of_abs_le hkey
    have hexp : (0 : ℝ) < Real.exp (L * t) := Real.exp_pos _
    rw [hF'def]
    have : 0 ≤ 2 * R t * (p t * DR t) * (1 / p t - Q t / K) + L * G t := by linarith
    positivity
  have hmain := le_of_continuousOn_of_deriv_nonneg hαβ hFc hFd hFnn
  simp only [hFdef] at hmain
  have hexpα : (0 : ℝ) < Real.exp (L * α) := Real.exp_pos _
  have hfac : Real.exp (L * β) = Real.exp (L * (β - α)) * Real.exp (L * α) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfac, ← mul_assoc] at hmain
  exact le_of_mul_le_mul_right hmain hexpα

/-- **The scaled amplitude cannot grow forwards faster than the exponential envelope.** -/
theorem sturmAmplitude_le_mul_exp' (hαβ : α ≤ β) (hK : 0 < K) (hM : 0 ≤ M)
    (hp : ∀ y ∈ Icc α β, p y ≠ 0)
    (hR : ∀ y ∈ Icc α β, HasDerivAt R (DR y) y)
    (hflux : ∀ y ∈ Icc α β, HasDerivAt (fun t => p t * DR t) (-(Q y * R y)) y)
    (hbound : ∀ y ∈ Icc α β, |1 / p y - Q y / K| ≤ M) :
    sturmAmplitude p R DR K β
      ≤ sturmAmplitude p R DR K α * Real.exp (M * Real.sqrt K * (β - α)) := by
  set G : ℝ → ℝ := sturmAmplitude p R DR K with hGdef
  set L : ℝ := M * Real.sqrt K with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    exact mul_nonneg hM (Real.sqrt_nonneg K)
  set F : ℝ → ℝ := fun y => -(G y * Real.exp (-(L * y))) with hFdef
  set F' : ℝ → ℝ := fun y =>
    -((2 * R y * (p y * DR y) * (1 / p y - Q y / K) - L * G y) * Real.exp (-(L * y))) with hF'def
  have hGc : ContinuousOn G (Icc α β) := continuousOn_sturmAmplitude hR hflux
  have hFc : ContinuousOn F (Icc α β) :=
    (hGc.mul (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).neg)).continuousOn).neg
  have hFd : ∀ t ∈ Ioo α β, HasDerivAt F (F' t) t := by
    intro t ht
    have htI : t ∈ Icc α β := ⟨ht.1.le, ht.2.le⟩
    have hG := hasDerivAt_sturmAmplitude (K := K) (Q := Q) hK.ne' (hp t htI) (hR t htI)
      (hflux t htI)
    have hE : HasDerivAt (fun y : ℝ => Real.exp (-(L * y))) (Real.exp (-(L * t)) * -L) t := by
      have h0 : HasDerivAt (fun y : ℝ => L * y) L t := by
        simpa using (hasDerivAt_id t).const_mul L
      have h1 : HasDerivAt (fun y : ℝ => -(L * y)) (-L) t := h0.neg
      simpa using h1.exp
    have h := (hG.mul hE).neg
    refine h.congr_deriv ?_
    rw [hF'def]
    ring
  have hFnn : ∀ t ∈ Ioo α β, 0 ≤ F' t := by
    intro t ht
    have htI : t ∈ Icc α β := ⟨ht.1.le, ht.2.le⟩
    have hcross := abs_two_mul_le_sqrt_mul_sturmAmplitude (p := p) (R := R) (DR := DR)
      (K := K) (y := t) hK
    have hb := hbound t htI
    have hGnn : 0 ≤ G t := sturmAmplitude_nonneg (p := p) (R := R) (DR := DR) hK
    have hkey : |2 * R t * (p t * DR t) * (1 / p t - Q t / K)| ≤ L * G t := by
      rw [abs_mul, hLdef]
      calc |2 * R t * (p t * DR t)| * |1 / p t - Q t / K|
          ≤ (Real.sqrt K * G t) * M := by
            refine mul_le_mul hcross hb (abs_nonneg _) ?_
            exact mul_nonneg (Real.sqrt_nonneg K) hGnn
        _ = M * Real.sqrt K * G t := by ring
    have hhigh : 2 * R t * (p t * DR t) * (1 / p t - Q t / K) ≤ L * G t := le_of_abs_le hkey
    have hexp : (0 : ℝ) < Real.exp (-(L * t)) := Real.exp_pos _
    rw [hF'def]
    have hneg : 2 * R t * (p t * DR t) * (1 / p t - Q t / K) - L * G t ≤ 0 := by linarith
    have := mul_nonpos_of_nonpos_of_nonneg hneg hexp.le
    linarith
  have hmain := le_of_continuousOn_of_deriv_nonneg hαβ hFc hFd hFnn
  simp only [hFdef] at hmain
  have hexpα : (0 : ℝ) < Real.exp (-(L * α)) := Real.exp_pos _
  have hexpγ : (0 : ℝ) < Real.exp (L * (β - α)) := Real.exp_pos _
  have hstep : G β * Real.exp (-(L * β)) ≤ G α * Real.exp (-(L * α)) := by linarith
  have hfac : Real.exp (-(L * β)) = (Real.exp (L * (β - α)))⁻¹ * Real.exp (-(L * α)) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  rw [hfac, ← mul_assoc] at hstep
  have h1 : G β * (Real.exp (L * (β - α)))⁻¹ ≤ G α := le_of_mul_le_mul_right hstep hexpα
  calc G β = G β * (Real.exp (L * (β - α)))⁻¹ * Real.exp (L * (β - α)) := by
        field_simp
    _ ≤ G α * Real.exp (L * (β - α)) := mul_le_mul_of_nonneg_right h1 hexpγ.le

end Envelope

/-! ## The variable scale

Letting the scale follow the potential turns the envelope from a local into a global tool: with
`K = −Q p` the factor `sqrt K · |1/p − Q/K|` becomes exactly twice the WKB rate `2 sqrt(−Q/p)`, and
the only extra cost is the logarithmic variation `|K'|/K` of the scale itself.  Across a barrier
that is one power of the scale ratio, whereas a constant scale would pay the full exponential.
-/

/-- The Sturm amplitude at a scale that varies along the interval. -/
def sturmAmplitudeVar (p R DR K : ℝ → ℝ) (y : ℝ) : ℝ := R y ^ 2 + (p y * DR y) ^ 2 / K y

theorem sturmAmplitudeVar_eq (p R DR K : ℝ → ℝ) (y : ℝ) :
    sturmAmplitudeVar p R DR K y = sturmAmplitude p R DR (K y) y := rfl

theorem sturmAmplitudeVar_nonneg {p R DR K : ℝ → ℝ} {y : ℝ} (hK : 0 < K y) :
    0 ≤ sturmAmplitudeVar p R DR K y := sturmAmplitude_nonneg hK

theorem sq_le_sturmAmplitudeVar {p R DR K : ℝ → ℝ} {y : ℝ} (hK : 0 < K y) :
    R y ^ 2 ≤ sturmAmplitudeVar p R DR K y := by
  rw [sturmAmplitudeVar]
  have : 0 ≤ (p y * DR y) ^ 2 / K y := by positivity
  linarith

theorem flux_sq_div_le_sturmAmplitudeVar {p R DR K : ℝ → ℝ} {y : ℝ} :
    (p y * DR y) ^ 2 / K y ≤ sturmAmplitudeVar p R DR K y := by
  rw [sturmAmplitudeVar]
  nlinarith [sq_nonneg (R y)]

/-- The derivative of the amplitude at a variable scale. -/
theorem hasDerivAt_sturmAmplitudeVar {p Q R DR K DK : ℝ → ℝ} {y : ℝ}
    (hK : K y ≠ 0) (hp : p y ≠ 0)
    (hR : HasDerivAt R (DR y) y)
    (hflux : HasDerivAt (fun t => p t * DR t) (-(Q y * R y)) y)
    (hKd : HasDerivAt K (DK y) y) :
    HasDerivAt (sturmAmplitudeVar p R DR K)
      (2 * R y * (p y * DR y) * (1 / p y - Q y / K y)
        - (p y * DR y) ^ 2 * DK y / K y ^ 2) y := by
  have h1 : HasDerivAt (fun t => R t ^ 2) (2 * R y * DR y) y := by
    have := hR.pow 2
    refine this.congr_deriv ?_
    ring
  have h2 : HasDerivAt (fun t => (p t * DR t) ^ 2 / K t)
      ((2 * (p y * DR y) * (-(Q y * R y)) * K y - (p y * DR y) ^ 2 * DK y) / K y ^ 2) y := by
    have hnum : HasDerivAt (fun t => (p t * DR t) ^ 2) (2 * (p y * DR y) * (-(Q y * R y))) y := by
      have := hflux.pow 2
      refine this.congr_deriv ?_
      ring
    exact hnum.div hKd hK
  have h := h1.add h2
  refine h.congr_deriv ?_
  field_simp
  ring

/-- The logarithmic derivative of the amplitude is bounded by twice the local wavenumber plus the
logarithmic variation of the scale. -/
theorem abs_deriv_sturmAmplitudeVar_le {p Q R DR K DK : ℝ → ℝ} {y : ℝ} (hK : 0 < K y) :
    |2 * R y * (p y * DR y) * (1 / p y - Q y / K y)
        - (p y * DR y) ^ 2 * DK y / K y ^ 2|
      ≤ (Real.sqrt (K y) * |1 / p y - Q y / K y| + |DK y| / K y)
          * sturmAmplitudeVar p R DR K y := by
  have hGnn : 0 ≤ sturmAmplitudeVar p R DR K y := sturmAmplitudeVar_nonneg hK
  have hcross : |2 * R y * (p y * DR y)| ≤ Real.sqrt (K y) * sturmAmplitudeVar p R DR K y :=
    abs_two_mul_le_sqrt_mul_sturmAmplitude hK
  have hflux : (p y * DR y) ^ 2 / K y ≤ sturmAmplitudeVar p R DR K y :=
    flux_sq_div_le_sturmAmplitudeVar
  have hterm1 : |2 * R y * (p y * DR y) * (1 / p y - Q y / K y)|
      ≤ Real.sqrt (K y) * |1 / p y - Q y / K y| * sturmAmplitudeVar p R DR K y := by
    rw [abs_mul]
    calc |2 * R y * (p y * DR y)| * |1 / p y - Q y / K y|
        ≤ (Real.sqrt (K y) * sturmAmplitudeVar p R DR K y) * |1 / p y - Q y / K y| :=
          mul_le_mul_of_nonneg_right hcross (abs_nonneg _)
      _ = Real.sqrt (K y) * |1 / p y - Q y / K y| * sturmAmplitudeVar p R DR K y := by ring
  have hterm2 : |(p y * DR y) ^ 2 * DK y / K y ^ 2|
      ≤ |DK y| / K y * sturmAmplitudeVar p R DR K y := by
    have hval : (p y * DR y) ^ 2 * DK y / K y ^ 2 = ((p y * DR y) ^ 2 / K y) * (DK y / K y) := by
      field_simp
    have hDK : |DK y / K y| = |DK y| / K y := by
      rw [abs_div, abs_of_pos hK]
    rw [hval, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (p y * DR y) ^ 2 / K y), hDK]
    calc (p y * DR y) ^ 2 / K y * (|DK y| / K y)
        ≤ sturmAmplitudeVar p R DR K y * (|DK y| / K y) :=
          mul_le_mul_of_nonneg_right hflux (by positivity)
      _ = |DK y| / K y * sturmAmplitudeVar p R DR K y := by ring
  calc |2 * R y * (p y * DR y) * (1 / p y - Q y / K y)
          - (p y * DR y) ^ 2 * DK y / K y ^ 2|
      ≤ |2 * R y * (p y * DR y) * (1 / p y - Q y / K y)|
          + |(p y * DR y) ^ 2 * DK y / K y ^ 2| := abs_sub _ _
    _ ≤ Real.sqrt (K y) * |1 / p y - Q y / K y| * sturmAmplitudeVar p R DR K y
          + |DK y| / K y * sturmAmplitudeVar p R DR K y := by linarith
    _ = (Real.sqrt (K y) * |1 / p y - Q y / K y| + |DK y| / K y)
          * sturmAmplitudeVar p R DR K y := by ring

/-- **The variable-scale amplitude envelope.**  The amplitude of a Sturm–Liouville solution is
trapped, in both directions, by the exponential of the accumulated majorant. -/
theorem sturmAmplitudeVar_envelope {p Q R DR K DK m : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hKpos : ∀ y ∈ Icc a b, 0 < K y)
    (hp : ∀ y ∈ Icc a b, p y ≠ 0)
    (hR : ∀ y ∈ Icc a b, HasDerivAt R (DR y) y)
    (hfluxd : ∀ y ∈ Icc a b, HasDerivAt (fun t => p t * DR t) (-(Q y * R y)) y)
    (hKd : ∀ y ∈ Icc a b, HasDerivAt K (DK y) y)
    (hGpos : ∀ y ∈ Icc a b, 0 < sturmAmplitudeVar p R DR K y)
    (hm : ContinuousOn m (Icc a b))
    (hbound : ∀ y ∈ Icc a b,
      Real.sqrt (K y) * |1 / p y - Q y / K y| + |DK y| / K y ≤ m y) :
    sturmAmplitudeVar p R DR K a
        ≤ sturmAmplitudeVar p R DR K b * Real.exp (∫ t in a..b, m t) ∧
      sturmAmplitudeVar p R DR K b
        ≤ sturmAmplitudeVar p R DR K a * Real.exp (∫ t in a..b, m t) := by
  set G : ℝ → ℝ := sturmAmplitudeVar p R DR K with hGdef
  set G' : ℝ → ℝ := fun y => 2 * R y * (p y * DR y) * (1 / p y - Q y / K y)
    - (p y * DR y) ^ 2 * DK y / K y ^ 2 with hG'def
  have hGd : ∀ y ∈ Icc a b, HasDerivAt G (G' y) y := fun y hy =>
    hasDerivAt_sturmAmplitudeVar (Q := Q) (hKpos y hy).ne' (hp y hy) (hR y hy) (hfluxd y hy)
      (hKd y hy)
  have hlow : ∀ y ∈ Icc a b, (-m y) * G y ≤ G' y := by
    intro y hy
    have habs := abs_deriv_sturmAmplitudeVar_le (p := p) (Q := Q) (R := R) (DR := DR)
      (K := K) (DK := DK) (y := y) (hKpos y hy)
    have hmy : Real.sqrt (K y) * |1 / p y - Q y / K y| + |DK y| / K y ≤ m y := hbound y hy
    have hGnn : 0 ≤ G y := (hGpos y hy).le
    have h1 : -(m y * G y) ≤ G' y := by
      have h2 : |G' y| ≤ (Real.sqrt (K y) * |1 / p y - Q y / K y| + |DK y| / K y) * G y := habs
      have h3 : (Real.sqrt (K y) * |1 / p y - Q y / K y| + |DK y| / K y) * G y ≤ m y * G y :=
        mul_le_mul_of_nonneg_right hmy hGnn
      have h4 : |G' y| ≤ m y * G y := le_trans h2 h3
      linarith [neg_le_of_abs_le h4, abs_le.mp h4]
    calc (-m y) * G y = -(m y * G y) := by ring
      _ ≤ G' y := h1
  have hup : ∀ y ∈ Icc a b, G' y ≤ m y * G y := by
    intro y hy
    have habs := abs_deriv_sturmAmplitudeVar_le (p := p) (Q := Q) (R := R) (DR := DR)
      (K := K) (DK := DK) (y := y) (hKpos y hy)
    have hmy : Real.sqrt (K y) * |1 / p y - Q y / K y| + |DK y| / K y ≤ m y := hbound y hy
    have hGnn : 0 ≤ G y := (hGpos y hy).le
    have h2 : |G' y| ≤ (Real.sqrt (K y) * |1 / p y - Q y / K y| + |DK y| / K y) * G y := habs
    have h3 : (Real.sqrt (K y) * |1 / p y - Q y / K y| + |DK y| / K y) * G y ≤ m y * G y :=
      mul_le_mul_of_nonneg_right hmy hGnn
    exact le_trans (le_of_abs_le (le_trans h2 h3)) le_rfl
  have hup' := le_mul_exp_integral_of_logDeriv_le' hab hGd hGpos hm hup
  have h1 := mul_exp_integral_le_of_logDeriv_ge' (L := fun t => -m t) hab hGd hGpos hm.neg hlow
  have hint : (∫ t in a..b, -m t) = -∫ t in a..b, m t := intervalIntegral.integral_neg
  rw [hint] at h1
  have hexp : (0 : ℝ) < Real.exp (∫ t in a..b, m t) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv] at h1
  exact ⟨(div_le_iff₀ hexp).mp h1, hup'⟩

end GaloisForLFunctions.HTGeometry

end
