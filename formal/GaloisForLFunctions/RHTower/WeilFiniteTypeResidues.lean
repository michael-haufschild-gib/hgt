import GaloisForLFunctions.RHTower.WeilFiniteTypeContinuation
import GaloisForLFunctions.RHTower.FiniteTypeDiscreteMomentAlgebra

/-!
# Finite-type Weil systems: residues at the zeros of `ζ`

**Boundary poles** (`boundary_pole_of_re_nonneg`).  Let `f` be continuous at `z₀`, `K ≥ 1`, and
`Re(f(s)/(s − z₀)^K) ≥ 0` on the half-disc `Re s > Re z₀`, `|s − z₀| < r`.  Then `f(z₀) = 0` if
`K ≥ 2`, and `f(z₀)` is real and `≥ 0` if `K = 1`.  (Along rays `s = z₀ + εw`, `Re w > 0`, one gets
`Re(f(z₀)/w^K) ≥ 0`, and by continuity also for `Re w ≥ 0`, `w ≠ 0`; the choices `w^K = ±1, ±i`
conclude.)

**Consequences for a full-cone Weil-positive finite-type system** `lam = Λ ⋆ a + μ ⋆ f + v`
(`A(s) = Σ a(n) n^{−s}`, `F(s) = Σ f(n) n^{−s}`), via the master identity of
`WeilFiniteTypeContinuation`:

* at a zero `ρ` with `Re ρ > ½`: `A(ρ) ζ'(ρ) = F(ρ)` (`dirPoly_mul_deriv_eq_of_offLine`);
* at a multiple zero on the critical line: `F(ρ) = 0` (`dirPoly_eq_zero_of_critical_multiple`);
* at a simple zero on the critical line the residue `A(ρ) − F(ρ)/ζ'(ρ)` of `Φ` is real and `≥ 0`
  (`residue_real_of_critical_simple`);
* hence at every critical zero, with `ζ(1 − s) = R(s) ζ(s)`,
  `R(ρ) ζ'(ρ) (A(ρ) − A(1 − ρ)) = R(ρ) F(ρ) + F(1 − ρ)` (`critical_realness`).
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
open RHTower.WeilSpectral RHTower.WeilHerglotz

namespace RHTower.WeilFiniteType

noncomputable section

/-! ## Boundary poles -/

/-- **Boundary poles of a function with nonnegative real part.** -/
theorem boundary_pole_of_re_nonneg {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousAt f z₀) {K : ℕ} (hK : 1 ≤ K)
    (hpos : ∀ s : ℂ, z₀.re < s.re → ‖s - z₀‖ < r → 0 ≤ (f s / (s - z₀) ^ K).re) :
    (2 ≤ K → f z₀ = 0) ∧ (K = 1 → (f z₀).im = 0 ∧ 0 ≤ (f z₀).re) := by
  set c := f z₀ with hc
  have hA : ∀ w : ℂ, 0 < w.re → 0 ≤ (c / w ^ K).re := by
    intro w hw
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have h1 : Tendsto (fun ε : ℝ => z₀ + (ε : ℂ) * w) (𝓝[>] 0) (𝓝 z₀) := by
      have : Tendsto (fun ε : ℝ => z₀ + (ε : ℂ) * w) (𝓝 0) (𝓝 (z₀ + ((0 : ℝ) : ℂ) * w)) :=
        ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun ε : ℝ => (f (z₀ + (ε : ℂ) * w) / w ^ K).re) (𝓝[>] 0)
        (𝓝 (c / w ^ K).re) :=
      (Complex.continuous_re.tendsto _).comp ((hf.tendsto.comp h1).div_const _)
    refine ge_of_tendsto hlim ?_
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < r / ‖w‖ :=
      nhdsWithin_le_nhds (eventually_lt_nhds (by positivity))
    filter_upwards [self_mem_nhdsWithin, hev] with ε hε hεr
    have hε0 : 0 < ε := hε
    have hre : z₀.re < (z₀ + (ε : ℂ) * w).re := by
      simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      nlinarith
    have hnorm : ‖z₀ + (ε : ℂ) * w - z₀‖ < r := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
      rwa [lt_div_iff₀ hwn] at hεr
    have hs := hpos _ hre hnorm
    have heq : f (z₀ + (ε : ℂ) * w) / (z₀ + (ε : ℂ) * w - z₀) ^ K =
        f (z₀ + (ε : ℂ) * w) / w ^ K * (((ε ^ K)⁻¹ : ℝ) : ℂ) := by
      rw [add_sub_cancel_left, mul_pow]
      push_cast
      have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0.ne'
      field_simp
    rw [heq, re_mul_ofReal] at hs
    exact (mul_nonneg_iff_of_pos_right (by positivity)).mp hs
  have hB : ∀ w : ℂ, w ≠ 0 → 0 ≤ w.re → 0 ≤ (c / w ^ K).re := by
    intro w hw0 hw
    have hcont : ContinuousAt (fun z : ℂ => (c / z ^ K).re) w :=
      Complex.continuous_re.continuousAt.comp
        (continuousAt_const.div (continuousAt_id.pow K) (pow_ne_zero K hw0))
    have h1 : Tendsto (fun δ : ℝ => w + (δ : ℂ)) (𝓝[>] 0) (𝓝 w) := by
      have : Tendsto (fun δ : ℝ => w + (δ : ℂ)) (𝓝 0) (𝓝 (w + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto (hcont.tendsto.comp h1) ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : 0 < δ := hδ
    exact hA _ (by simp; linarith)
  have hI : (c / I).re = c.im := by rw [div_I]; simp
  have hnI : (c / -I).re = -c.im := by rw [div_neg, div_I]; simp
  have hre1 : 0 ≤ c.re := by simpa using hB 1 one_ne_zero (by simp)
  refine ⟨fun hK2 => ?_, fun hK1 => ?_⟩
  · have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have hKne : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
    have hpow : ∀ θ : ℝ, cexp ((θ : ℂ) * I) ^ K = cexp ((K : ℂ) * ((θ : ℂ) * I)) := fun θ =>
      (Complex.exp_nat_mul _ K).symm
    have hcos : ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi / 2 → 0 ≤ (cexp ((θ : ℂ) * I)).re ∧
        0 ≤ (cexp (((-θ : ℝ) : ℂ) * I)).re := by
      intro θ h0 h1
      rw [exp_ofReal_mul_I_re, exp_ofReal_mul_I_re]
      exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩,
        Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩⟩
    have hK2' : (2 : ℝ) ≤ K := by exact_mod_cast hK2
    have hθ1 : Real.pi / K ≤ Real.pi / 2 := div_le_div_of_nonneg_left Real.pi_pos.le two_pos hK2'
    have hθ2 : Real.pi / (2 * K) ≤ Real.pi / 2 :=
      div_le_div_of_nonneg_left Real.pi_pos.le two_pos (by linarith)
    -- `w^K = −1`
    have hm1 : cexp (((Real.pi / K : ℝ) : ℂ) * I) ^ K = -1 := by
      rw [hpow, show (K : ℂ) * (((Real.pi / K : ℝ) : ℂ) * I) = (Real.pi : ℂ) * I by
        push_cast; field_simp, exp_pi_mul_I]
    have hI' : cexp (((Real.pi / (2 * K) : ℝ) : ℂ) * I) ^ K = I := by
      rw [hpow, show (K : ℂ) * (((Real.pi / (2 * K) : ℝ) : ℂ) * I) = (Real.pi : ℂ) / 2 * I by
        push_cast; field_simp, exp_pi_div_two_mul_I]
    have hmI : cexp (((-(Real.pi / (2 * K)) : ℝ) : ℂ) * I) ^ K = -I := by
      rw [hpow, show (K : ℂ) * (((-(Real.pi / (2 * K)) : ℝ) : ℂ) * I) = -(Real.pi : ℂ) / 2 * I by
        push_cast; field_simp, exp_neg_pi_div_two_mul_I]
    have h1 := hB _ (Complex.exp_ne_zero _)
      (hcos (Real.pi / K) (by positivity) hθ1).1
    have h2 := hB _ (Complex.exp_ne_zero _)
      (hcos (Real.pi / (2 * K)) (by positivity) hθ2).1
    have h3 := hB _ (Complex.exp_ne_zero _)
      (hcos (Real.pi / (2 * K)) (by positivity) hθ2).2
    rw [hm1, div_neg, div_one, neg_re] at h1
    rw [hI', hI] at h2
    rw [hmI, hnI] at h3
    apply Complex.ext <;> simp <;> linarith
  · subst hK1
    have h2 := hB I I_ne_zero (by simp)
    have h3 := hB (-I) (neg_ne_zero.mpr I_ne_zero) (by simp)
    rw [pow_one, hI] at h2
    rw [pow_one, hnI] at h3
    exact ⟨by linarith, hre1⟩

/-! ## The zeros of `Z₁ = (s − 1) ζ(s)` -/

theorem analyticOrderAt_zetaResidueUnit_ne_top (ρ : ℂ) :
    analyticOrderAt zetaResidueUnit ρ ≠ ⊤ := by
  have hZ : AnalyticOnNhd ℂ zetaResidueUnit univ := fun s _ => analyticAt_zetaResidueUnit s
  refine hZ.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (x := 1) trivial
    trivial ?_
  rw [(analyticAt_zetaResidueUnit 1).analyticOrderAt_eq_zero.mpr (by simp)]
  exact ENat.zero_ne_top

theorem zetaResidueUnit_eq_zero_iff {s : ℂ} (hs : s ≠ 1) :
    zetaResidueUnit s = 0 ↔ riemannZeta s = 0 := by
  rw [(zetaResidueUnit_eventuallyEq hs).eq_of_nhds, mul_eq_zero, sub_eq_zero]
  simp [hs]

theorem deriv_zetaResidueUnit_of_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    deriv zetaResidueUnit ρ = (ρ - 1) * deriv riemannZeta ρ := by
  rw [deriv_zetaResidueUnit_eq hρ1, hz, zero_add]

/-! ## Off-line zeros -/

/-- **No poles right of the critical line**: `A(ρ) ζ'(ρ) = F(ρ)` at every zero with `Re ρ > ½`. -/
theorem dirPoly_mul_deriv_eq_of_offLine {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {ρ : ℂ} (hρ : 1 / 2 < ρ.re)
    (hz : riemannZeta ρ = 0) : dirPoly N a ρ * deriv riemannZeta ρ = dirPoly N f ρ := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; exact riemannZeta_one_ne_zero hz
  have h := zeta_mul_eq ha hf hf1 hv hW hρ hρ1
  rw [hz, zero_mul] at h
  exact (sub_eq_zero.mp h.symm)

/-! ## Critical zeros -/

/-- On the half-disc at a critical zero `ρ` of order `m`, `Φ(s) = g(s)/(s − ρ)^m` with `g`
continuous at `ρ` and `g(ρ) = (ρ − 1)(A(ρ)ζ'(ρ) − F(ρ))/u(ρ)`, where `Z₁ = (s − ρ)^m u`. -/
theorem exists_boundary_quotient {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hz : riemannZeta ρ = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ u : ℂ → ℂ, AnalyticAt ℂ u ρ ∧ u ρ ≠ 0 ∧
      (∀ᶠ s in 𝓝 ρ, zetaResidueUnit s = (s - ρ) ^ m * u s) ∧
      ∃ g : ℂ → ℂ, ContinuousAt g ρ ∧
        g ρ = (ρ - 1) * (dirPoly N a ρ * deriv riemannZeta ρ - dirPoly N f ρ) / u ρ ∧
        ∃ r : ℝ, 0 < r ∧ ∀ s : ℂ, ρ.re < s.re → ‖s - ρ‖ < r →
          0 ≤ (g s / (s - ρ) ^ m).re := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; norm_num at hρ
  have hρ0 : ρ ≠ 0 := by rintro rfl; norm_num at hρ
  have hZρ : zetaResidueUnit ρ = 0 := (zetaResidueUnit_eq_zero_iff hρ1).mpr hz
  obtain ⟨u, hu, hu0, hfac⟩ :=
    ((analyticAt_zetaResidueUnit ρ).analyticOrderAt_ne_top).mp
      (analyticOrderAt_zetaResidueUnit_ne_top ρ)
  set m := analyticOrderNatAt zetaResidueUnit ρ with hm
  have hm1 : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    have := hfac.eq_of_nhds
    rw [hm0, pow_zero, one_smul] at this
    exact hu0 (this ▸ hZρ)
  obtain ⟨η₀, hη₀, hEd⟩ := hv.holo
  set P := masterRight N a f with hP
  set g : ℂ → ℂ := fun s => (s - ρ) ^ m * (zetaArchimedeanDatum s - E s + 1 / (s - 1)) +
    P s / (u s * (s - 1)) with hg
  have hρm1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hGc : ContinuousAt zetaArchimedeanDatum ρ :=
    (differentiableAt_zetaArchimedeanDatum (by rw [hρ]; norm_num)).continuousAt
  have hEc : ContinuousAt E ρ :=
    (hEd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by show 1 / 2 - η₀ < ρ.re; rw [hρ]; linarith))).continuousAt
  have hPc : ContinuousAt P ρ := (analyticOnNhd_masterRight N a f ρ trivial).continuousAt
  have hgc : ContinuousAt g ρ := by
    refine ((continuousAt_id.sub continuousAt_const).pow m |>.mul
      ((hGc.sub hEc).add (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        hρm1))).add (hPc.div (hu.continuousAt.mul (continuousAt_id.sub continuousAt_const))
        (mul_ne_zero hu0 hρm1))
  refine ⟨m, hm1, u, hu, hu0, ?_, g, hgc, ?_, ?_⟩
  · filter_upwards [hfac] with s hs
    simp only [hs, smul_eq_mul]
  · have hPρ : P ρ = (ρ - 1) ^ 2 * (dirPoly N a ρ * deriv riemannZeta ρ - dirPoly N f ρ) := by
      rw [hP]
      unfold masterRight
      rw [deriv_zetaResidueUnit_of_zero hρ1 hz, hZρ]
      ring
    simp only [hg, sub_self, zero_pow (by omega : m ≠ 0), zero_mul, zero_add, hPρ]
    field_simp
  · -- a punctured neighbourhood where `u ≠ 0` and `s ≠ 1`
    have hev : ∀ᶠ s in 𝓝 ρ, u s ≠ 0 ∧ s ≠ 1 ∧
        zetaResidueUnit s = (s - ρ) ^ m * u s ∧ 1 / 2 - η₀ < s.re :=
      (hu.continuousAt.eventually_ne hu0).and ((eventually_ne_nhds hρ1).and
        ((hfac.mono fun s hs => by simp only [hs, smul_eq_mul]).and
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
            (by show 1 / 2 - η₀ < ρ.re; rw [hρ]; linarith))))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨r, hr, fun s hs hsr => ?_⟩
    obtain ⟨hus, hs1, hZs, -⟩ := hball (by rwa [dist_eq_norm])
    have hsρ : s ≠ ρ := by rintro rfl; exact lt_irrefl _ hs
    have hs' : 1 / 2 < s.re := by rw [hρ] at hs; exact hs
    have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hmaster := master_identity ha hf hf1 hv hW hs'
    unfold masterLeft at hmaster
    rw [hZs] at hmaster
    have hmaster' : (s - ρ) ^ m * u s *
        ((s - 1) * (weilContinuation hW s - zetaArchimedeanDatum s + E s) - 1) = P s := hmaster
    have hΦ : weilContinuation hW s = g s / (s - ρ) ^ m := by
      rw [eq_div_iff (pow_ne_zero m hsρ')]
      simp only [hg]
      rw [← hmaster']
      field_simp
      ring
    rw [← hΦ]
    exact re_weilContinuation_nonneg hW hs'

/-- **Multiple critical zeros**: `F(ρ) = 0`. -/
theorem dirPoly_eq_zero_of_critical_multiple {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hz : riemannZeta ρ = 0) (hd : deriv riemannZeta ρ = 0) : dirPoly N f ρ = 0 := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; norm_num at hρ
  obtain ⟨m, hm1, u, hu, hu0, hfac, g, hgc, hgρ, r, hr, hpos⟩ :=
    exists_boundary_quotient ha hf hf1 hv hW hρ hz
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm : m = 1 := by omega
    subst hm
    -- `Z₁'(ρ) = u(ρ) ≠ 0`, but `Z₁'(ρ) = (ρ − 1) ζ'(ρ) = 0`
    have hderiv : HasDerivAt zetaResidueUnit (u ρ) ρ := by
      have h1 : HasDerivAt (fun s => (s - ρ) * u s) (1 * u ρ + (ρ - ρ) * deriv u ρ) ρ :=
        ((hasDerivAt_id' ρ).sub_const ρ).mul hu.differentiableAt.hasDerivAt
      rw [sub_self, zero_mul, add_zero, one_mul] at h1
      exact h1.congr_of_eventuallyEq (hfac.mono fun s hs => by rw [hs, pow_one])
    have := hderiv.deriv
    rw [deriv_zetaResidueUnit_of_zero hρ1 hz, hd, mul_zero] at this
    exact hu0 this.symm
  have hg0 := (boundary_pole_of_re_nonneg hr hgc hm1 hpos).1 hm2
  rw [hgρ, hd, mul_zero, zero_sub, div_eq_zero_iff] at hg0
  rcases hg0 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (sub_eq_zero.mp h') hρ1
    · exact neg_eq_zero.mp h'
  · exact absurd h hu0

/-- **Simple critical zeros**: the residue `A(ρ) − F(ρ)/ζ'(ρ)` of `Φ` is real and `≥ 0`. -/
theorem residue_real_of_critical_simple {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hz : riemannZeta ρ = 0) (hd : deriv riemannZeta ρ ≠ 0) :
    (dirPoly N a ρ - dirPoly N f ρ / deriv riemannZeta ρ).im = 0 ∧
      0 ≤ (dirPoly N a ρ - dirPoly N f ρ / deriv riemannZeta ρ).re := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; norm_num at hρ
  have hρm1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  obtain ⟨m, hm1, u, hu, hu0, hfac, g, hgc, hgρ, r, hr, hpos⟩ :=
    exists_boundary_quotient ha hf hf1 hv hW hρ hz
  -- the order is one, and `u(ρ) = Z₁'(ρ) = (ρ − 1) ζ'(ρ)`
  have hm : m = 1 := by
    by_contra hne
    have hm2 : 2 ≤ m := by omega
    have hderiv : HasDerivAt zetaResidueUnit 0 ρ := by
      have h1 : HasDerivAt (fun s => (s - ρ) ^ m * u s)
          (((m : ℂ) * (ρ - ρ) ^ (m - 1) * 1) * u ρ + (ρ - ρ) ^ m * deriv u ρ) ρ :=
        (((hasDerivAt_id ρ).sub_const ρ).pow m).mul hu.differentiableAt.hasDerivAt
      have hz1 : (ρ - ρ) ^ (m - 1) = 0 := by rw [sub_self]; exact zero_pow (by omega)
      have hz2 : (ρ - ρ) ^ m = 0 := by rw [sub_self]; exact zero_pow (by omega)
      rw [hz1, hz2] at h1
      simp only [mul_zero, zero_mul, add_zero] at h1
      exact h1.congr_of_eventuallyEq hfac
    have := hderiv.deriv
    rw [deriv_zetaResidueUnit_of_zero hρ1 hz] at this
    exact hd ((mul_eq_zero.mp this).resolve_left hρm1)
  subst hm
  have huρ : u ρ = (ρ - 1) * deriv riemannZeta ρ := by
    have hderiv : HasDerivAt zetaResidueUnit (u ρ) ρ := by
      have h1 : HasDerivAt (fun s => (s - ρ) * u s) (1 * u ρ + (ρ - ρ) * deriv u ρ) ρ :=
        ((hasDerivAt_id' ρ).sub_const ρ).mul hu.differentiableAt.hasDerivAt
      rw [sub_self, zero_mul, add_zero, one_mul] at h1
      exact h1.congr_of_eventuallyEq (hfac.mono fun s hs => by rw [hs, pow_one])
    rw [← hderiv.deriv, deriv_zetaResidueUnit_of_zero hρ1 hz]
  have hres := (boundary_pole_of_re_nonneg hr hgc le_rfl hpos).2 rfl
  have hval : g ρ = dirPoly N a ρ - dirPoly N f ρ / deriv riemannZeta ρ := by
    rw [hgρ, huρ]
    field_simp
  rwa [hval] at hres

/-- `A(conj s) = conj A(s)` for real coefficients. -/
theorem dirPoly_conj (N : ℕ) (a : ℕ → ℝ) (s : ℂ) :
    dirPoly N a (conj s) = conj (dirPoly N a s) := by
  unfold dirPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  rw [map_mul, Complex.conj_ofReal, ← map_neg, Complex.cpow_conj _ _ harg, Complex.conj_natCast]

theorem deriv_riemannZeta_conj' (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj']

/-- **Realness at every critical zero.**  With `ζ(1 − s) = R(s) ζ(s)`,
`R(ρ) ζ'(ρ) (A(ρ) − A(1 − ρ)) = R(ρ) F(ρ) + F(1 − ρ)`. -/
theorem critical_realness {N : ℕ} {a f v : ℕ → ℝ} {E : ℂ → ℂ}
    (ha : SupportedIn N a) (hf : SupportedIn N f) (hf1 : f 1 = 0) (hv : RegularPart v E)
    (hW : WeilPositiveFull (finiteTypeSeq a f v)) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hz : riemannZeta ρ = 0) :
    zetaReflectionFactor ρ * deriv riemannZeta ρ * (dirPoly N a ρ - dirPoly N a (1 - ρ)) =
      zetaReflectionFactor ρ * dirPoly N f ρ + dirPoly N f (1 - ρ) := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; norm_num at hρ
  have hconj : 1 - ρ = conj ρ := by
    apply Complex.ext <;> simp [hρ]; norm_num
  by_cases hd : deriv riemannZeta ρ = 0
  · have hF := dirPoly_eq_zero_of_critical_multiple ha hf hf1 hv hW hρ hz hd
    rw [hd, hconj]
    simp [dirPoly_conj, hF]
  · obtain ⟨him, -⟩ := residue_real_of_critical_simple ha hf hf1 hv hW hρ hz hd
    set c := dirPoly N a ρ - dirPoly N f ρ / deriv riemannZeta ρ with hc
    have hcc : conj c = c := Complex.conj_eq_iff_im.mpr him
    have hd1 : deriv riemannZeta (1 - ρ) = -(zetaReflectionFactor ρ * deriv riemannZeta ρ) :=
      deriv_riemannZeta_one_sub_eq_of_zero (by rw [hρ]; norm_num) hρ1 hz
    have hR0 : zetaReflectionFactor ρ * deriv riemannZeta ρ ≠ 0 := by
      intro h
      rw [h, neg_zero, hconj, deriv_riemannZeta_conj'] at hd1
      exact hd ((map_eq_zero _).mp hd1)
    -- `conj c = A(1 − ρ) − F(1 − ρ)/ζ'(1 − ρ)`
    have hcc' : conj c = dirPoly N a (1 - ρ) - dirPoly N f (1 - ρ) / deriv riemannZeta (1 - ρ) := by
      rw [hc, map_sub, map_div₀, ← dirPoly_conj, ← dirPoly_conj, ← deriv_riemannZeta_conj', hconj]
    rw [hcc, hd1] at hcc'
    rw [hc] at hcc'
    have hR : zetaReflectionFactor ρ ≠ 0 := left_ne_zero_of_mul hR0
    field_simp at hcc'
    linear_combination hcc'

end

end RHTower.WeilFiniteType
