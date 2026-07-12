import GaloisForLFunctions.RHTower.BornEtaGrading
import GaloisForLFunctions.RHTower.CompletedBornReflectionNoGo
import GaloisForLFunctions.Hurwitz.HurwitzZeta

/-!
# The Born self-duality lifts as an order/disorder sector exchange

The parity-graded completed sector `Λ₄(s) = (1 - 2^{1-s})·Λ(s)` — the archimedean factor times
the paired eta supertrace — cannot be reflection-symmetric: its reflection cocycle is the
two-adic quotient `(1-2^s)/(1-2^{1-s})`.  This module shows how the self-duality of the
completed zeta survives the grading: the reflection **exchanges sectors**.  Fourier duality of
the two-torsion sends the parity character `n ↦ (-1)^n` to the half-integer coset `ℤ + 1/2`,
and correspondingly the reflection maps the parity sector to the negative of the half-shift
sector `Λ₂(s) = (2^s - 1)·Λ(s)`, whose Dirichlet series is the trace over the displaced levels
`m + 1/2`:

`Λ₄(1-s) = -Λ₂(s)`,  `∑ (m+1/2)^{-s} = (2^s - 1)·ζ(s)`.

The two sectors split the two poles of the completed zeta between them and swap their
convergence regimes: the parity sector converges as a supertrace on the whole temperature
strip, keeps the single pole at the archimedean end `s = 0` (`s·Λ₄ → 1`), and is regular at
the ungraded transition `s = 1` with the finite supertrace value `log 2 = Γℝ(1)·η(1)`; the
half-shift sector is an ordinary trace converging only in the low-temperature region, with its
single pole at `s = 1` (`(s-1)·Λ₂ → 1`).  High-temperature graded order and low-temperature
displaced disorder are exchanged by the reflection with a sign — the Kramers–Wannier shape of
the completed functional equation over the prime `2`.
-/

noncomputable section

namespace RHTower

open Complex Filter

/-- The parity-graded (order) completed sector: the deleted-two completed zeta,
equal to `Γℝ · (paired eta supertrace)` on the right half-plane. -/
def lambdaParity (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ (1 - s)) * completedRiemannZeta s

/-- The half-shift (disorder) completed sector: the completed trace of the displaced levels
`ℤ + 1/2`. -/
def lambdaHalfShift (s : ℂ) : ℂ := ((2 : ℂ) ^ s - 1) * completedRiemannZeta s

/-- The parity sector is the graded weld: archimedean factor times the paired eta
supertrace. -/
theorem lambdaParity_eq_graded {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) :
    lambdaParity s = Complex.Gammaℝ s * etaPair s :=
  (Gammaℝ_mul_etaPair h0 h1).symm

/-! ## The sector exchange -/

/-- **The sector exchange.**  The functional-equation reflection maps the parity-graded
sector to the negative of the half-shift sector: the self-duality of the completed zeta
lifts through the grading as an order/disorder exchange with a sign, never as a symmetry of
the graded sector alone. -/
theorem lambdaParity_one_sub (s : ℂ) : lambdaParity (1 - s) = -lambdaHalfShift s := by
  unfold lambdaParity lambdaHalfShift
  rw [completedRiemannZeta_one_sub, show (1 : ℂ) - (1 - s) = s by ring]
  ring

/-- The converse exchange: reflecting the disorder sector returns the negative of the order
sector, so the signed swap is an involution on the sector pair. -/
theorem lambdaHalfShift_one_sub (s : ℂ) : lambdaHalfShift (1 - s) = -lambdaParity s := by
  have h := lambdaParity_one_sub (1 - s)
  rw [show (1 : ℂ) - (1 - s) = s by ring] at h
  linear_combination h

/-- The exchange in Born-temperature form: `Z₄(2-β) = -Z₂(β)` for the half-dilated
sectors. -/
theorem lambdaParity_born_reflect (β : ℂ) :
    lambdaParity ((2 - β) / 2) = -lambdaHalfShift (β / 2) := by
  rw [show (2 - β) / 2 = 1 - β / 2 by ring, lambdaParity_one_sub]

/-! ## The disorder sector is the half-integer level trace -/

/-- The grading-odd level sum: the Dirichlet trace over the odd integer levels — the range
of the parity-odd projection `1 - μ₂μ₂*`. -/
def oddLevelZeta (s : ℂ) : ℂ := ∑' k : ℕ, (((2 * k : ℕ) : ℂ) + 1) ^ (-s)

/-- **The grading-odd trace is the deleted-even zeta**: `∑ (2k+1)^{-s} = (1 - 2^{-s})·ζ(s)`
for `Re s > 1`. -/
theorem oddLevelZeta_eq {s : ℂ} (hs : 1 < s.re) :
    oddLevelZeta s = (1 - (2 : ℂ) ^ (-s)) * riemannZeta s := by
  set f : ℕ → ℂ := fun n => ((n : ℂ) + 1) ^ (-s) with hf
  have hsum : Summable f := HurwitzZetaShift.summable_hurwitzSeries hs 1
  have he : Summable fun k : ℕ => f (2 * k) :=
    hsum.comp_injective fun a b hab => by omega
  have ho : Summable fun k : ℕ => f (2 * k + 1) :=
    hsum.comp_injective fun a b hab => by omega
  have hζ : riemannZeta s = ∑' n : ℕ, f n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact tsum_congr fun n => by
      show 1 / ((n : ℂ) + 1) ^ s = ((n : ℂ) + 1) ^ (-s)
      rw [Complex.cpow_neg, one_div]
  have heo : (∑' k : ℕ, f (2 * k)) + ∑' k : ℕ, f (2 * k + 1) = ∑' n : ℕ, f n :=
    tsum_even_add_odd he ho
  have heven_term : ∀ k : ℕ, f (2 * k + 1) = (2 : ℂ) ^ (-s) * f k := by
    intro k
    show (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s) = (2 : ℂ) ^ (-s) * (((k : ℕ) : ℂ) + 1) ^ (-s)
    have hbase : (((2 * k + 1 : ℕ) : ℂ) + 1) = ((2 : ℕ) : ℂ) * (((k + 1 : ℕ)) : ℂ) := by
      push_cast
      ring
    have h2 : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_num
    have hk1 : (((k + 1 : ℕ)) : ℂ) = ((k : ℕ) : ℂ) + 1 := by push_cast; ring
    rw [hbase, natCast_mul_natCast_cpow, h2, hk1]
  have hev : ∑' k : ℕ, f (2 * k + 1) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    calc ∑' k : ℕ, f (2 * k + 1) = ∑' k : ℕ, (2 : ℂ) ^ (-s) * f k :=
          tsum_congr heven_term
      _ = (2 : ℂ) ^ (-s) * ∑' k : ℕ, f k := tsum_mul_left
      _ = (2 : ℂ) ^ (-s) * riemannZeta s := by rw [← hζ]
  have hsplit := heo
  rw [hev, ← hζ] at hsplit
  have hodd : oddLevelZeta s = ∑' k : ℕ, f (2 * k) := by
    rw [oddLevelZeta]
  rw [hodd]
  linear_combination hsplit

/-- **The disorder sector is the `μ₂`-twisted grading-odd sector.**  The half-integer levels
are the odd integer levels displaced by one half `2`-dilation quantum:
`∑ (m+1/2)^{-s} = 2^s · ∑ (2k+1)^{-s}`, unconditionally.  The `ℤ+1/2` module is hosted by
the same `log √n` system: it is the grading-odd subspace with the Hamiltonian shifted by
`-½ log 2`. -/
theorem hzeta_one_half_eq_twisted_odd (s : ℂ) :
    HurwitzZetaShift.hzeta s (1 / 2) = (2 : ℂ) ^ s * oddLevelZeta s := by
  have hodd_term : ∀ k : ℕ,
      ((k : ℂ) + 1 / 2) ^ (-s) = (2 : ℂ) ^ s * ((((2 * k : ℕ)) : ℂ) + 1) ^ (-s) := by
    intro k
    have hcast : ((k : ℂ) + 1 / 2) = ((((2 * k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    have harg : (2 : ℂ).arg ≠ Real.pi := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_ne_zero.symm
    have hhalfpow : (((1 / 2 : ℝ)) : ℂ) ^ (-s) = (2 : ℂ) ^ s := by
      rw [show (((1 / 2 : ℝ)) : ℂ) = ((2 : ℂ))⁻¹ by norm_num,
        Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]
    have hbase : ((((2 * k + 1 : ℕ) : ℝ)) : ℂ) ^ (-s) = (((2 * k : ℕ) : ℂ) + 1) ^ (-s) := by
      congr 1
      push_cast
      ring
    rw [hcast, Complex.ofReal_mul,
      mul_cpow_ofReal_nonneg (by positivity) (by norm_num), hhalfpow, hbase, mul_comm]
  calc HurwitzZetaShift.hzeta s (1 / 2)
      = ∑' k : ℕ, ((k : ℂ) + 1 / 2) ^ (-s) := rfl
    _ = ∑' k : ℕ, (2 : ℂ) ^ s * ((((2 * k : ℕ)) : ℂ) + 1) ^ (-s) := tsum_congr hodd_term
    _ = (2 : ℂ) ^ s * ∑' k : ℕ, ((((2 * k : ℕ)) : ℂ) + 1) ^ (-s) := tsum_mul_left
    _ = (2 : ℂ) ^ s * oddLevelZeta s := rfl

/-- **The half-shift Dirichlet identity.**  For `Re s > 1` the trace over the displaced
levels `m + 1/2` is `(2^s - 1)·ζ(s)`: the half-integer coset — the Fourier dual of the parity
character — carries exactly the reflected deleted-two factor. -/
theorem hzeta_one_half {s : ℂ} (hs : 1 < s.re) :
    HurwitzZetaShift.hzeta s (1 / 2) = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  have hcancel : (2 : ℂ) ^ s * (2 : ℂ) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ two_ne_zero]
    simp
  rw [hzeta_one_half_eq_twisted_odd, oddLevelZeta_eq hs]
  linear_combination (-(riemannZeta s)) * hcancel

/-- **Sector doubling is one rung of the `2`-dilation tower**: adjoining the twisted sector
to the untwisted one reproduces the full system at half-quantum shift, spectrum `½ℕ`:
`∑ (m+1/2)^{-s} + ζ(s) = 2^s·ζ(s)` for `Re s > 1`. -/
theorem hzeta_one_half_add_zeta {s : ℂ} (hs : 1 < s.re) :
    HurwitzZetaShift.hzeta s (1 / 2) + riemannZeta s = (2 : ℂ) ^ s * riemannZeta s := by
  rw [hzeta_one_half hs]
  ring

/-- The completed disorder sector is the completed half-integer trace on `Re s > 1`. -/
theorem lambdaHalfShift_eq_halfLevels {s : ℂ} (hs : 1 < s.re) :
    lambdaHalfShift s = Complex.Gammaℝ s * HurwitzZetaShift.hzeta s (1 / 2) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hG : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [hzeta_one_half hs]
  unfold lambdaHalfShift
  rw [riemannZeta_def_of_ne_zero hs0]
  field_simp

/-! ## The split pole pair -/

/-- The parity sector keeps the single simple pole at the archimedean end:
`s · Λ₄(s) → 1` as `s → 0`. -/
theorem tendsto_mul_lambdaParity_zero :
    Tendsto (fun s : ℂ => s * lambdaParity s) (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 1) := by
  have hcont : Continuous fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s) :=
    continuous_const.sub
      (Continuous.const_cpow (continuous_const.sub continuous_id) (Or.inl two_ne_zero))
  have hc : Tendsto (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) (nhdsWithin 0 {(0 : ℂ)}ᶜ)
      (nhds (1 - 2)) := by
    have hval : (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - 0) = 1 - 2 := by
      rw [show ((1 : ℂ) - 0) = 1 by ring, Complex.cpow_one]
    rw [← hval]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := hc.mul tendsto_mul_completedRiemannZeta_zero
  rw [show ((1 : ℂ) - 2) * (-1) = 1 by ring] at h
  exact h.congr fun s => by
    unfold lambdaParity
    ring

/-- The disorder sector carries the reflected pole: `(s-1) · Λ₂(s) → 1` as `s → 1`. -/
theorem tendsto_mul_lambdaHalfShift_one :
    Tendsto (fun s : ℂ => (s - 1) * lambdaHalfShift s) (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 1) := by
  have hmap : Tendsto (fun s : ℂ => 1 - s) (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Continuous fun s : ℂ => (1 : ℂ) - s := continuous_const.sub continuous_id
      have hval : (1 : ℂ) - 1 = 0 := by ring
      rw [← hval]
      exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      exact hs (sub_eq_zero.mp h).symm
  have h := tendsto_mul_lambdaParity_zero.comp hmap
  exact h.congr fun s => by
    simp only [Function.comp_apply]
    rw [lambdaParity_one_sub]
    ring

/-- **The graded sector is regular at the ungraded transition**, with the finite supertrace
value `log 2 = Γℝ(1)·η(1)`: the parity grading removes the pole that marks the Bost–Connes
transition and replaces it by the convergent alternating value. -/
theorem tendsto_lambdaParity_one :
    Tendsto lambdaParity (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (Complex.log 2)) := by
  have hg : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).const_sub 1
  have hc : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ ((1 : ℂ) - w))
      ((2 : ℂ) ^ ((1 : ℂ) - 1) * Complex.log 2 * (-1)) 1 :=
    hg.const_cpow (Or.inl two_ne_zero)
  have hf : HasDerivAt (fun w : ℂ => 1 - (2 : ℂ) ^ ((1 : ℂ) - w)) (Complex.log 2) 1 := by
    have h := hc.const_sub 1
    have hval : -((2 : ℂ) ^ ((1 : ℂ) - 1) * Complex.log 2 * (-1)) = Complex.log 2 := by
      rw [show ((1 : ℂ) - 1) = 0 by ring, Complex.cpow_zero]
      ring
    rw [hval] at h
    exact h
  have hslope := hasDerivAt_iff_tendsto_slope.mp hf
  have hT1 : Tendsto
      (fun z : ℂ => (1 - (2 : ℂ) ^ (1 - z)) * (completedRiemannZeta₀ z - 1 / z))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 0) := by
    have hcoup : Continuous fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z) :=
      continuous_const.sub
        (Continuous.const_cpow (continuous_const.sub continuous_id) (Or.inl two_ne_zero))
    have h1z : ContinuousAt (fun z : ℂ => 1 / z) 1 :=
      ContinuousAt.div continuousAt_const continuousAt_id one_ne_zero
    have hcont : ContinuousAt
        (fun z : ℂ => (1 - (2 : ℂ) ^ (1 - z)) * (completedRiemannZeta₀ z - 1 / z)) 1 :=
      hcoup.continuousAt.mul
        ((differentiable_completedZeta₀.continuous.continuousAt).sub h1z)
    have hval : (1 - (2 : ℂ) ^ ((1 : ℂ) - 1)) * (completedRiemannZeta₀ 1 - 1 / 1) = 0 := by
      rw [show ((1 : ℂ) - 1) = 0 by ring, Complex.cpow_zero]
      ring
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hcomb := hT1.add hslope
  rw [zero_add] at hcomb
  refine hcomb.congr' ?_
  have hne0 : ∀ᶠ z : ℂ in nhdsWithin 1 {(1 : ℂ)}ᶜ, z ≠ 0 :=
    (eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hne0] with z hz1' hz0
  have hz1 : z ≠ 1 := hz1'
  have hsub1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hsub1' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  rw [slope_def_field]
  show (1 - (2 : ℂ) ^ (1 - z)) * (completedRiemannZeta₀ z - 1 / z)
      + ((1 - (2 : ℂ) ^ ((1 : ℂ) - z)) - (1 - (2 : ℂ) ^ ((1 : ℂ) - 1))) / (z - 1)
      = lambdaParity z
  rw [show ((1 : ℂ) - 1) = 0 by ring, Complex.cpow_zero]
  unfold lambdaParity
  rw [completedRiemannZeta_eq]
  field_simp
  ring

end RHTower
