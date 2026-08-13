import Mathlib
import GaloisForLFunctions.HTGeometry.FiniteAmplifierPatternCap

/-!
# The abstract pole-purchase frame: master bound, width cap, threshold, and stability

The single-`σ` pole-purchase engine consists of channels `h g` indexed by a finite amplifier
support `S` with a distinguished pole channel `e` and zero channel `g₀`, subject to the
source-cone inequality (a nonnegative pattern pairs nonnegatively with the channels), the
pole bound on `h e`, the zero bound on `h g₀`, and the two-sided input bound on every other
channel.  This module certifies:

* **the master bound** — at `σ = 1 + a/𝔏`, every zero of real coordinate `β ≥ 1 − δ` forces
  `c_{g₀} m/(a + δ𝔏) ≤ c_e/a + (∑|c|)·A`;
* **zero exclusion and the width cap** — when the pattern data beat the bound strictly, the
  zero is excluded (`β < 1 − δ`), and every derivable exclusion width obeys
  `δ𝔏 < C(pattern data)`: the `1/𝔏` shape is forced;
* **the threshold** — a strict exclusion at any positive width forces `c_e < c_{g₀} m`:
  detection must strictly out-weigh the pole (the ratio threshold `ρ > 1` at `m = 1`);
* **stability** — the width cap survives finite multi-`σ` derivations verbatim, and any
  positive-measure average of channel inequalities that is strictly exclusive contains a
  pointwise strictly exclusive parameter, so averaged derivations inherit the cap;
* **coefficient finiteness on the circle** — a nonnegative cosine pattern of degree `m` has
  every coefficient bounded by twice its constant term (`|a_k| ≤ 2a₀`), by discrete
  root-of-unity averaging against the nonnegative kernels `1 ± cos`; hence the
  detection/pole ratio of the circle support is finite.

Together with the two-point cap and circle witness of `FiniteAmplifierPatternCap`, this is
the frame-level content of the finite-amplifier barrier: no finite amplifier family of any
size reaches beyond width `C/𝔏` inside the frame, and the family lever is capped by a
finite extremal ratio.
-/

namespace HTGeometry

noncomputable section

open Finset

/-! ## The master bound of the single-`σ` derivation -/

/-- **The master bound.**  In the abstract frame, a zero of real coordinate `β ≥ 1 − δ`
forces the pattern-data inequality `c_{g₀} m/(a + δ𝔏) ≤ c_e/a + (∑_{g∈S}|c_g|)·A` at the
evaluation point `σ = 1 + a/𝔏`. -/
theorem frame_master_bound {G : Type*} [DecidableEq G] (S : Finset G) (e g₀ : G)
    (he : e ∈ S) (hg₀ : g₀ ∈ S) (hne : e ≠ g₀) (h c : G → ℝ)
    {A m L β δ a σ : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hm : 0 ≤ m) (hδ : 0 ≤ δ) (hA : 0 ≤ A)
    (hce : 0 ≤ c e) (hcg : 0 ≤ c g₀)
    (hσ : σ = 1 + a / L) (hβσ : β < σ) (hβ : 1 - δ ≤ β)
    (hP1 : 0 ≤ ∑ g ∈ S, c g * h g)
    (hP2 : h e ≤ 1 / (σ - 1) + A * L)
    (hP3z : h g₀ ≤ -(m / (σ - β)) + A * L)
    (hP3o : ∀ g ∈ S, g ≠ e → g ≠ g₀ → |h g| ≤ A * L) :
    c g₀ * m / (a + δ * L) ≤ c e / a + (∑ g ∈ S, |c g|) * A := by
  have hσ1 : σ - 1 = a / L := by rw [hσ]; ring
  have hσ1pos : 0 < σ - 1 := by rw [hσ1]; positivity
  have hσβpos : 0 < σ - β := by linarith
  have hpole : 1 / (σ - 1) = L / a := by
    rw [hσ1]
    field_simp
  have hdenom : 0 < a + δ * L := by positivity
  -- the zero bound transported to the width denominator
  have hgap : σ - β ≤ (a + δ * L) / L := by
    have h1 : σ - β ≤ σ - (1 - δ) := by linarith
    have h2 : σ - (1 - δ) = (a + δ * L) / L := by
      rw [hσ]
      field_simp
      ring
    linarith [h2 ▸ h1]
  have hzero_frac : m * L / (a + δ * L) ≤ m / (σ - β) := by
    have h1 : m / ((a + δ * L) / L) ≤ m / (σ - β) :=
      div_le_div_of_nonneg_left hm hσβpos hgap
    have h2 : m / ((a + δ * L) / L) = m * L / (a + δ * L) := by
      rw [div_div_eq_mul_div]
    linarith [h2 ▸ h1]
  -- split the source-cone sum at the two distinguished channels
  set R : Finset G := (S.erase e).erase g₀ with hR
  have hg₀e : g₀ ∈ S.erase e := Finset.mem_erase.mpr ⟨hne.symm, hg₀⟩
  have hsplit : ∑ g ∈ S, c g * h g
      = c e * h e + (c g₀ * h g₀ + ∑ g ∈ R, c g * h g) := by
    rw [hR, Finset.add_sum_erase _ (fun g => c g * h g) hg₀e,
      Finset.add_sum_erase _ (fun g => c g * h g) he]
  have habsAL : ∀ g ∈ R, c g * h g ≤ |c g| * (A * L) := by
    intro g hgR
    have hg1 : g ≠ g₀ := (Finset.mem_erase.mp hgR).1
    have hg2 : g ≠ e := (Finset.mem_erase.mp (Finset.mem_erase.mp hgR).2).1
    have hgS : g ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hgR).2).2
    calc c g * h g ≤ |c g * h g| := le_abs_self _
      _ = |c g| * |h g| := abs_mul _ _
      _ ≤ |c g| * (A * L) :=
          mul_le_mul_of_nonneg_left (hP3o g hgS hg2 hg1) (abs_nonneg _)
  have htail : ∑ g ∈ R, c g * h g ≤ (∑ g ∈ R, |c g|) * (A * L) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum habsAL
  have hpolebd : c e * h e ≤ c e * (L / a + A * L) := by
    refine mul_le_mul_of_nonneg_left ?_ hce
    rw [← hpole]
    exact hP2
  have hzerobd : c g₀ * h g₀ ≤ c g₀ * (-(m * L / (a + δ * L)) + A * L) := by
    refine mul_le_mul_of_nonneg_left ?_ hcg
    have := hzero_frac
    linarith [hP3z]
  -- assemble
  have hmain : 0 ≤ c e * (L / a + A * L)
      + (c g₀ * (-(m * L / (a + δ * L)) + A * L) + (∑ g ∈ R, |c g|) * (A * L)) := by
    calc (0 : ℝ) ≤ ∑ g ∈ S, c g * h g := hP1
      _ = c e * h e + (c g₀ * h g₀ + ∑ g ∈ R, c g * h g) := hsplit
      _ ≤ _ := by
          have := htail
          have := hpolebd
          have := hzerobd
          linarith
  -- the absolute-coefficient sum dominates the assembled coefficients
  have hcoeff : c e + c g₀ + ∑ g ∈ R, |c g| ≤ ∑ g ∈ S, |c g| := by
    have hsplit2 : ∑ g ∈ S, |c g| = |c e| + (|c g₀| + ∑ g ∈ R, |c g|) := by
      rw [hR, Finset.add_sum_erase _ (fun g => |c g|) hg₀e,
        Finset.add_sum_erase _ (fun g => |c g|) he]
    rw [hsplit2, abs_of_nonneg hce, abs_of_nonneg hcg]
    linarith
  have hL' : c g₀ * m * L / (a + δ * L)
      ≤ c e * (L / a) + (∑ g ∈ S, |c g|) * (A * L) := by
    have hALnn : 0 ≤ A * L := by positivity
    have hstep : c g₀ * (m * L / (a + δ * L))
        ≤ c e * (L / a) + (c e + c g₀ + ∑ g ∈ R, |c g|) * (A * L) := by nlinarith [hmain]
    have hmono : (c e + c g₀ + ∑ g ∈ R, |c g|) * (A * L)
        ≤ (∑ g ∈ S, |c g|) * (A * L) := mul_le_mul_of_nonneg_right hcoeff hALnn
    calc c g₀ * m * L / (a + δ * L) = c g₀ * (m * L / (a + δ * L)) := by ring
      _ ≤ c e * (L / a) + (c e + c g₀ + ∑ g ∈ R, |c g|) * (A * L) := hstep
      _ ≤ c e * (L / a) + (∑ g ∈ S, |c g|) * (A * L) := by linarith
  -- divide by 𝔏
  have hfinal : c g₀ * m / (a + δ * L) * L
      ≤ (c e / a + (∑ g ∈ S, |c g|) * A) * L := by
    calc c g₀ * m / (a + δ * L) * L = c g₀ * m * L / (a + δ * L) := by ring
      _ ≤ c e * (L / a) + (∑ g ∈ S, |c g|) * (A * L) := hL'
      _ = (c e / a + (∑ g ∈ S, |c g|) * A) * L := by ring
  exact le_of_mul_le_mul_right hfinal hL

/-- **Zero exclusion.**  When the pattern data beat the master bound strictly, no zero with
`β ≥ 1 − δ` exists in the frame: the derivation concludes `β < 1 − δ`. -/
theorem frame_zero_exclusion {G : Type*} [DecidableEq G] (S : Finset G) (e g₀ : G)
    (he : e ∈ S) (hg₀ : g₀ ∈ S) (hne : e ≠ g₀) (h c : G → ℝ)
    {A m L β δ a σ : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hm : 0 ≤ m) (hδ : 0 ≤ δ) (hA : 0 ≤ A)
    (hce : 0 ≤ c e) (hcg : 0 ≤ c g₀)
    (hσ : σ = 1 + a / L) (hβσ : β < σ)
    (hP1 : 0 ≤ ∑ g ∈ S, c g * h g)
    (hP2 : h e ≤ 1 / (σ - 1) + A * L)
    (hP3z : h g₀ ≤ -(m / (σ - β)) + A * L)
    (hP3o : ∀ g ∈ S, g ≠ e → g ≠ g₀ → |h g| ≤ A * L)
    (hexcl : c e / a + (∑ g ∈ S, |c g|) * A < c g₀ * m / (a + δ * L)) :
    β < 1 - δ := by
  by_contra hcontra
  push Not at hcontra
  have := frame_master_bound S e g₀ he hg₀ hne h c hL ha hm hδ hA hce hcg hσ hβσ hcontra
    hP1 hP2 hP3z hP3o
  linarith

/-- **The width cap in the frame (Theorem 1).**  A strictly exclusive pattern bounds its own
width: `δ𝔏 < c_{g₀}m/(c_e/a + (∑|c|)A) − a`, a constant of the pattern data alone.  Every
derivable zero-exclusion inside the frame has width `O(1/𝔏)`. -/
theorem frame_width_of_exclusion {G : Type*} [DecidableEq G] (S : Finset G) (e g₀ : G)
    (c : G → ℝ) {A m L δ a : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hce : 0 < c e)
    (hexcl : c e / a + (∑ g ∈ S, |c g|) * A < c g₀ * m / (a + δ * L)) :
    δ * L < c g₀ * m / (c e / a + (∑ g ∈ S, |c g|) * A) - a := by
  have hK : 0 ≤ (∑ g ∈ S, |c g|) * A :=
    mul_nonneg (Finset.sum_nonneg fun g _ => abs_nonneg _) hA
  have hδL : 0 ≤ δ * L := by positivity
  exact width_cap ha hδL hce hK hexcl

/-- **The threshold (Theorem 2, INV7.3).**  A strict exclusion at any nonnegative width
forces the detection coefficient strictly past the pole coefficient: `c_e < c_{g₀}·m`.  At
`m = 1` this is the ratio threshold `ρ > 1`; on `ℤ/2` the two-point cap shows the threshold
unreachable — Page's barrier. -/
theorem frame_threshold_necessity {G : Type*} [DecidableEq G] (S : Finset G) (e g₀ : G)
    (c : G → ℝ) {A m L δ a : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hce : 0 ≤ c e)
    (hexcl : c e / a + (∑ g ∈ S, |c g|) * A < c g₀ * m / (a + δ * L)) :
    c e < c g₀ * m := by
  have hK : 0 ≤ (∑ g ∈ S, |c g|) * A :=
    mul_nonneg (Finset.sum_nonneg fun g _ => abs_nonneg _) hA
  have hdenom : 0 < a + δ * L := by positivity
  have h1 : c e / a < c g₀ * m / (a + δ * L) := by linarith
  have h2 : c e / a * (a + δ * L) < c g₀ * m := (lt_div_iff₀ hdenom).mp h1
  have h3 : c e ≤ c e / a * (a + δ * L) := by
    have hδLnn : 0 ≤ δ * L := by positivity
    have : c e / a * (a + δ * L) = c e + c e / a * (δ * L) := by
      field_simp
    rw [this]
    have : 0 ≤ c e / a * (δ * L) := by positivity
    linarith
  linarith

/-! ## Stability of the cap (Theorem 1′) -/

/-- **Multi-`σ` stability.**  A finite family of evaluation points `σ_j = 1 + a_j/𝔏` with
patterns `c_j`, jointly strictly exclusive, still bounds the width:
`δ𝔏 < m·(∑_j c_{g₀,j}) / (∑_j (c_{e,j}/a_j + K_j))`.  The finite multi-`σ` derivation class
adds nothing beyond the single-`σ` cap. -/
theorem multi_sigma_width_cap {J : Type*} (T : Finset J) (cg ce K a : J → ℝ)
    {m δ L : ℝ} (hm : 0 ≤ m) (hδL : 0 < δ * L)
    (ha : ∀ j ∈ T, 0 < a j) (hcg : ∀ j ∈ T, 0 ≤ cg j)
    (hpos : 0 < ∑ j ∈ T, (ce j / a j + K j))
    (hexcl : ∑ j ∈ T, (ce j / a j + K j) < ∑ j ∈ T, cg j * m / (a j + δ * L)) :
    δ * L < m * (∑ j ∈ T, cg j) / (∑ j ∈ T, (ce j / a j + K j)) := by
  have hterm : ∀ j ∈ T, cg j * m / (a j + δ * L) ≤ cg j * m / (δ * L) := by
    intro j hj
    have h1 : δ * L ≤ a j + δ * L := by linarith [ha j hj]
    exact div_le_div_of_nonneg_left (mul_nonneg (hcg j hj) hm) hδL h1
  have hsum : ∑ j ∈ T, cg j * m / (a j + δ * L) ≤ (∑ j ∈ T, cg j) * m / (δ * L) := by
    calc ∑ j ∈ T, cg j * m / (a j + δ * L) ≤ ∑ j ∈ T, cg j * m / (δ * L) :=
          Finset.sum_le_sum hterm
      _ = (∑ j ∈ T, cg j) * m / (δ * L) := by
          rw [← Finset.sum_div, ← Finset.sum_mul]
  have hchain : ∑ j ∈ T, (ce j / a j + K j) < (∑ j ∈ T, cg j) * m / (δ * L) :=
    lt_of_lt_of_le hexcl hsum
  have h2 : (∑ j ∈ T, (ce j / a j + K j)) * (δ * L) < (∑ j ∈ T, cg j) * m :=
    (lt_div_iff₀ hδL).mp hchain
  rw [lt_div_iff₀ hpos]
  calc δ * L * (∑ j ∈ T, (ce j / a j + K j))
      = (∑ j ∈ T, (ce j / a j + K j)) * (δ * L) := by ring
    _ < (∑ j ∈ T, cg j) * m := h2
    _ = m * (∑ j ∈ T, cg j) := by ring

/-- **Averaged derivations contain pointwise ones.**  A positive-measure average of channel
inequalities that is strictly exclusive must be strictly exclusive at some parameter:
integration cannot create an exclusion that no member of the family has. -/
theorem averaged_exclusion_pointwise {P : Type*} [MeasurableSpace P]
    (μ : MeasureTheory.Measure P) (lhs rhs : P → ℝ)
    (hl : MeasureTheory.Integrable lhs μ) (hr : MeasureTheory.Integrable rhs μ)
    (havg : ∫ p, rhs p ∂μ < ∫ p, lhs p ∂μ) : ∃ p, rhs p < lhs p := by
  by_contra hno
  push Not at hno
  exact absurd (MeasureTheory.integral_mono hl hr hno) (not_le.mpr havg)

/-- **Averaged stability.**  If every pointwise strict exclusion in an admissible family
carries the width cap, so does any strictly exclusive positive average over the family. -/
theorem averaged_width_cap {P : Type*} [MeasurableSpace P]
    (μ : MeasureTheory.Measure P) (lhs rhs : P → ℝ)
    (hl : MeasureTheory.Integrable lhs μ) (hr : MeasureTheory.Integrable rhs μ)
    {δ L C : ℝ} (hpt : ∀ p, rhs p < lhs p → δ * L < C)
    (havg : ∫ p, rhs p ∂μ < ∫ p, lhs p ∂μ) : δ * L < C := by
  obtain ⟨p, hp⟩ := averaged_exclusion_pointwise μ lhs rhs hl hr havg
  exact hpt p hp

/-! ## Coefficient finiteness on the circle (Theorem 2.1, ℤ anchor) -/

open Complex in
theorem exp_unit_sum_zero (N : ℕ) (r : ℕ) (hr : 0 < r) (hrN : r < N) :
    ∑ j ∈ Finset.range N, Complex.exp (2 * Real.pi * I * r * j / N) = 0 := by
  have hNpos : 0 < N := lt_trans hr hrN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  set x : ℂ := Complex.exp (2 * Real.pi * I * r / N) with hx
  have hterm : ∀ j : ℕ, Complex.exp (2 * Real.pi * I * r * j / N) = x ^ j := by
    intro j
    rw [hx, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hxN : x ^ N = 1 := by
    rw [hx, ← Complex.exp_nat_mul]
    have harg : (N : ℂ) * (2 * Real.pi * I * r / N) = (r : ℂ) * (2 * Real.pi * I) := by
      field_simp
    rw [harg]
    have := Complex.exp_int_mul_two_pi_mul_I (r : ℤ)
    have hcast : ((r : ℤ) : ℂ) = (r : ℂ) := by push_cast; rfl
    rw [hcast] at this
    convert this using 2

  have hxne : x ≠ 1 := by
    rw [hx]
    intro hcontra
    have hre := congrArg Complex.re hcontra
    have hargx : 2 * (Real.pi : ℂ) * I * r / N = ((2 * Real.pi * r / N : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [hargx, Complex.exp_ofReal_mul_I_re, Complex.one_re] at hre
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hre
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hθpos : 0 < 2 * Real.pi * r / N := by
      have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
      positivity
    have hθlt : 2 * Real.pi * r / N < 2 * Real.pi := by
      rw [div_lt_iff₀ hNr]
      have hrN' : (r : ℝ) < N := by exact_mod_cast hrN
      nlinarith [Real.pi_pos]
    have hnpos : (0 : ℝ) < n * (2 * Real.pi) := hn ▸ hθpos
    have hnlt : (n : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by
      rw [hn, one_mul]
      exact hθlt
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have hn0 : 0 < n := by
      by_contra hn0
      push Not at hn0
      have : (n : ℝ) ≤ 0 := by exact_mod_cast hn0
      nlinarith
    have hn1 : n < 1 := by
      by_contra hn1
      push Not at hn1
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      nlinarith
    omega
  calc ∑ j ∈ Finset.range N, Complex.exp (2 * Real.pi * I * r * j / N)
      = ∑ j ∈ Finset.range N, x ^ j := Finset.sum_congr rfl fun j _ => hterm j
    _ = (x ^ N - 1) / (x - 1) := geom_sum_eq hxne N
    _ = 0 := by rw [hxN]; simp

theorem cos_sample_sum_zero (N : ℕ) (r : ℕ) (hr : 0 < r) (hrN : r < N) :
    ∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * r * j / N) = 0 := by
  have hNpos : 0 < N := lt_trans hr hrN
  have := congrArg Complex.re (exp_unit_sum_zero N r hr hrN)
  rw [Complex.re_sum] at this
  simp only [Complex.zero_re] at this
  calc ∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * r * j / N)
      = ∑ j ∈ Finset.range N, (Complex.exp (2 * Real.pi * Complex.I * r * j / N)).re := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have harg : 2 * Real.pi * Complex.I * r * j / N
            = ((2 * Real.pi * r * j / N : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [harg, Complex.exp_ofReal_mul_I_re]
    _ = 0 := this

/-- The sampled cosine at frequency difference: even in the frequency, so the vanishing
covers both orders of a frequency pair. -/
private theorem cos_sample_diff (N k l j : ℕ) :
    Real.cos (2 * Real.pi * k * j / N) * Real.cos (2 * Real.pi * l * j / N)
      = (Real.cos (2 * Real.pi * (k - l : ℝ) * j / N)
        + Real.cos (2 * Real.pi * (k + l : ℝ) * j / N)) / 2 := by
  have hsub := Real.cos_sub (2 * Real.pi * k * j / N) (2 * Real.pi * l * j / N)
  have hadd := Real.cos_add (2 * Real.pi * k * j / N) (2 * Real.pi * l * j / N)
  have h1 : 2 * Real.pi * k * j / N - 2 * Real.pi * l * j / N
      = 2 * Real.pi * (k - l : ℝ) * j / N := by ring
  have h2 : 2 * Real.pi * k * j / N + 2 * Real.pi * l * j / N
      = 2 * Real.pi * (k + l : ℝ) * j / N := by ring
  rw [← h1, ← h2, hsub, hadd]
  ring

/-- **Coefficient bound for nonnegative cosine patterns (Theorem 2.1, circle anchor).**
Every coefficient of a pointwise-nonnegative cosine pattern of degree `m` is at most twice
the constant term: discrete averaging over `2m+1` equispaced samples against the
nonnegative kernels `1 ± cos(k₀θ)` isolates `a₀ ± a_{k₀}/2 ≥ 0`.  The detection/pole ratio
of every finite circle support is therefore finite (at most `2`). -/
theorem cosine_pattern_coeff_bound (m : ℕ) (a : ℕ → ℝ)
    (hpos : ∀ θ : ℝ, 0 ≤ a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θ))
    (k₀ : ℕ) (hk₀ : k₀ ∈ Finset.Icc 1 m) :
    |a k₀| ≤ 2 * a 0 := by
  obtain ⟨hk₀1, hk₀m⟩ := Finset.mem_Icc.mp hk₀
  set N : ℕ := 2 * m + 1 with hN
  have hNpos : 0 < N := by omega
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  set θj : ℕ → ℝ := fun j => 2 * Real.pi * j / N with hθj
  -- sampled sums of a single frequency
  have hfreq : ∀ r : ℕ, 0 < r → r < N →
      ∑ j ∈ Finset.range N, Real.cos (r * θj j) = 0 := by
    intro r hr hrN
    have := cos_sample_sum_zero N r hr hrN
    calc ∑ j ∈ Finset.range N, Real.cos (r * θj j)
        = ∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * r * j / N) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hθj]
          congr 1
          ring
      _ = 0 := this
  -- the sampled pattern sum
  have hPsum : ∑ j ∈ Finset.range N,
      (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j)) = N * a 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    have hzero : ∑ j ∈ Finset.range N, ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j)
        = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k hk => ?_
      obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
      rw [← Finset.mul_sum]
      rw [hfreq k hk1 (by omega)]
      ring
    rw [hzero]
    simp [nsmul_eq_mul]
  -- the sampled pattern-times-kernel sum
  have hPcos : ∑ j ∈ Finset.range N,
      (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j)) * Real.cos (k₀ * θj j)
      = N * (a k₀ / 2) := by
    have hexp : ∀ j ∈ Finset.range N,
        (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j)) * Real.cos (k₀ * θj j)
        = a 0 * Real.cos (k₀ * θj j)
          + ∑ k ∈ Finset.Icc 1 m,
              a k * (Real.cos (k * θj j) * Real.cos (k₀ * θj j)) := by
      intro j _
      rw [add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib]
    have hconst : ∑ j ∈ Finset.range N, a 0 * Real.cos (k₀ * θj j) = 0 := by
      rw [← Finset.mul_sum, hfreq k₀ hk₀1 (by omega)]
      ring
    rw [hconst, zero_add, Finset.sum_comm]
    have hkterm : ∀ k ∈ Finset.Icc 1 m,
        ∑ j ∈ Finset.range N, a k * (Real.cos (k * θj j) * Real.cos (k₀ * θj j))
        = if k = k₀ then (N : ℝ) * (a k₀ / 2) else 0 := by
      intro k hk
      obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
      have hprod : ∀ j : ℕ, Real.cos (k * θj j) * Real.cos (k₀ * θj j)
          = (Real.cos (2 * Real.pi * (k - k₀ : ℝ) * j / N)
            + Real.cos (2 * Real.pi * (k + k₀ : ℝ) * j / N)) / 2 := by
        intro j
        have h1 : (k : ℝ) * θj j = 2 * Real.pi * k * j / N := by rw [hθj]; ring
        have h2 : (k₀ : ℝ) * θj j = 2 * Real.pi * k₀ * j / N := by rw [hθj]; ring
        rw [h1, h2]
        exact cos_sample_diff N k k₀ j
      have hsumsum : ∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * (k + k₀ : ℝ) * j / N)
          = 0 := by
        have hcast : ∀ j : ℕ, Real.cos (2 * Real.pi * (k + k₀ : ℝ) * j / N)
            = Real.cos (2 * Real.pi * ((k + k₀ : ℕ) : ℝ) * j / N) := by
          intro j
          congr 2
          push_cast
          ring
        rw [Finset.sum_congr rfl fun j _ => hcast j]
        exact cos_sample_sum_zero N (k + k₀) (by omega) (by omega)
      by_cases hkk : k = k₀
      · subst hkk
        rw [if_pos rfl]
        have hdiag : ∀ j : ℕ, Real.cos (2 * Real.pi * (k - k : ℝ) * j / N) = 1 := by
          intro j
          norm_num
        calc ∑ j ∈ Finset.range N, a k * (Real.cos (k * θj j) * Real.cos (k * θj j))
            = ∑ j ∈ Finset.range N, a k *
                ((Real.cos (2 * Real.pi * (k - k : ℝ) * j / N)
                  + Real.cos (2 * Real.pi * (k + k : ℝ) * j / N)) / 2) := by
              exact Finset.sum_congr rfl fun j _ => by rw [hprod j]
          _ = ∑ j ∈ Finset.range N, (a k / 2
                + a k * Real.cos (2 * Real.pi * (k + k : ℝ) * j / N) / 2) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hdiag j]
              ring
          _ = (N : ℝ) * (a k / 2) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
              have : ∑ j ∈ Finset.range N,
                  a k * Real.cos (2 * Real.pi * (k + k : ℝ) * j / N) / 2
                  = (∑ j ∈ Finset.range N,
                      Real.cos (2 * Real.pi * (k + k : ℝ) * j / N)) * (a k / 2) := by
                rw [← Finset.sum_div, ← Finset.mul_sum]
                ring
              rw [this, hsumsum]
              simp [nsmul_eq_mul]
      · simp only [if_neg hkk]
        have hdiffsum : ∑ j ∈ Finset.range N,
            Real.cos (2 * Real.pi * (k - k₀ : ℝ) * j / N) = 0 := by
          rcases lt_or_gt_of_ne hkk with hlt | hgt
          · have hcast : ∀ j : ℕ, Real.cos (2 * Real.pi * (k - k₀ : ℝ) * j / N)
                = Real.cos (2 * Real.pi * ((k₀ - k : ℕ) : ℝ) * j / N) := by
              intro j
              rw [← Real.cos_neg (2 * Real.pi * (k - k₀ : ℝ) * j / N)]
              congr 1
              have : ((k₀ - k : ℕ) : ℝ) = (k₀ : ℝ) - k := by
                push_cast [Nat.cast_sub hlt.le]
                ring
              rw [this]
              ring
            rw [Finset.sum_congr rfl fun j _ => hcast j]
            exact cos_sample_sum_zero N (k₀ - k) (by omega) (by omega)
          · have hcast : ∀ j : ℕ, Real.cos (2 * Real.pi * (k - k₀ : ℝ) * j / N)
                = Real.cos (2 * Real.pi * ((k - k₀ : ℕ) : ℝ) * j / N) := by
              intro j
              congr 2
              push_cast [Nat.cast_sub hgt.le]
              ring
            rw [Finset.sum_congr rfl fun j _ => hcast j]
            exact cos_sample_sum_zero N (k - k₀) (by omega) (by omega)
        calc ∑ j ∈ Finset.range N, a k * (Real.cos (k * θj j) * Real.cos (k₀ * θj j))
            = ∑ j ∈ Finset.range N, (a k * Real.cos (2 * Real.pi * (k - k₀ : ℝ) * j / N) / 2
                + a k * Real.cos (2 * Real.pi * (k + k₀ : ℝ) * j / N) / 2) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hprod j]
              ring
          _ = 0 := by
              rw [Finset.sum_add_distrib]
              have e1 : ∑ j ∈ Finset.range N,
                  a k * Real.cos (2 * Real.pi * (k - k₀ : ℝ) * j / N) / 2
                  = (∑ j ∈ Finset.range N,
                      Real.cos (2 * Real.pi * (k - k₀ : ℝ) * j / N)) * (a k / 2) := by
                rw [← Finset.sum_div, ← Finset.mul_sum]
                ring
              have e2 : ∑ j ∈ Finset.range N,
                  a k * Real.cos (2 * Real.pi * (k + k₀ : ℝ) * j / N) / 2
                  = (∑ j ∈ Finset.range N,
                      Real.cos (2 * Real.pi * (k + k₀ : ℝ) * j / N)) * (a k / 2) := by
                rw [← Finset.sum_div, ← Finset.mul_sum]
                ring
              rw [e1, e2, hdiffsum, hsumsum]
              ring
    rw [Finset.sum_congr rfl hkterm, Finset.sum_ite_eq' (Finset.Icc 1 m) k₀]
    rw [if_pos hk₀]
  -- the two nonnegative kernel averages
  have hplus : 0 ≤ (N : ℝ) * a 0 + (N : ℝ) * (a k₀ / 2) := by
    have := Finset.sum_nonneg (s := Finset.range N)
      (f := fun j => (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j))
        * (1 + Real.cos (k₀ * θj j)))
      (fun j _ => mul_nonneg (hpos (θj j)) (by nlinarith [Real.neg_one_le_cos (k₀ * θj j)]))
    have hexpand : ∑ j ∈ Finset.range N,
        (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j)) * (1 + Real.cos (k₀ * θj j))
        = (N : ℝ) * a 0 + (N : ℝ) * (a k₀ / 2) := by
      have : ∀ j ∈ Finset.range N,
          (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j)) * (1 + Real.cos (k₀ * θj j))
          = (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j))
            + (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j)) * Real.cos (k₀ * θj j) := by
        intro j _
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hPsum, hPcos]
    linarith [hexpand ▸ this]
  have hminus : 0 ≤ (N : ℝ) * a 0 - (N : ℝ) * (a k₀ / 2) := by
    have := Finset.sum_nonneg (s := Finset.range N)
      (f := fun j => (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j))
        * (1 - Real.cos (k₀ * θj j)))
      (fun j _ => mul_nonneg (hpos (θj j)) (by nlinarith [Real.cos_le_one (k₀ * θj j)]))
    have hexpand : ∑ j ∈ Finset.range N,
        (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j)) * (1 - Real.cos (k₀ * θj j))
        = (N : ℝ) * a 0 - (N : ℝ) * (a k₀ / 2) := by
      have : ∀ j ∈ Finset.range N,
          (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j)) * (1 - Real.cos (k₀ * θj j))
          = (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j))
            - (a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θj j)) * Real.cos (k₀ * θj j) := by
        intro j _
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, hPsum, hPcos]
    linarith [hexpand ▸ this]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- The circle detection/pole ratio is finite: every normalized nonnegative cosine pattern
has detection coefficient at most `2`. -/
theorem cosine_pattern_ratio_finite (m : ℕ) (a : ℕ → ℝ) (ha0 : a 0 = 1)
    (hpos : ∀ θ : ℝ, 0 ≤ a 0 + ∑ k ∈ Finset.Icc 1 m, a k * Real.cos (k * θ))
    (k₀ : ℕ) (hk₀ : k₀ ∈ Finset.Icc 1 m) :
    a k₀ ≤ 2 := by
  have := cosine_pattern_coeff_bound m a hpos k₀ hk₀
  rw [ha0] at this
  have := abs_le.mp this
  linarith [this.2]

end

end HTGeometry

namespace HTGeometry

/-- **The ratio controls the constant (Theorem 2, cap form).**  Under the ratio bound
`c_{g₀} ≤ ρ·c_e`, the width cap is controlled by `ρ` alone:
`δ𝔏 < ρ·c_e·m/(c_e/a + K) − a`, increasing in `ρ`.  The pattern lever of the frame is
exactly the extremal ratio of its support. -/
theorem frame_width_ratio_form {G : Type*} [DecidableEq G] (S : Finset G) (e g₀ : G)
    (c : G → ℝ) {A m L δ a ρ : ℝ}
    (hL : 0 < L) (ha : 0 < a) (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hce : 0 < c e) (hm : 0 ≤ m)
    (hρ : c g₀ ≤ ρ * c e)
    (hexcl : c e / a + (∑ g ∈ S, |c g|) * A < c g₀ * m / (a + δ * L)) :
    δ * L < ρ * c e * m / (c e / a + (∑ g ∈ S, |c g|) * A) - a := by
  have hbase := frame_width_of_exclusion S e g₀ c hL ha hδ hA hce hexcl
  have hK : 0 ≤ (∑ g ∈ S, |c g|) * A :=
    mul_nonneg (Finset.sum_nonneg fun g _ => abs_nonneg _) hA
  have hden : 0 < c e / a + (∑ g ∈ S, |c g|) * A := by positivity
  have hnum : c g₀ * m ≤ ρ * c e * m :=
    mul_le_mul_of_nonneg_right hρ hm
  have hmono : c g₀ * m / (c e / a + (∑ g ∈ S, |c g|) * A)
      ≤ ρ * c e * m / (c e / a + (∑ g ∈ S, |c g|) * A) := by gcongr
  linarith

end HTGeometry

namespace HTGeometry

open Finset ComplexConjugate

/-- Dual-sum orthogonality on a finite abelian group: the characters at a fixed nonzero
element sum to zero. -/
private theorem sum_addChar_eq_zero {G : Type*} [AddCommGroup G] [Fintype G]
    (a : G) (ha : a ≠ 0) : ∑ ψ : AddChar G ℂ, ψ a = 0 := by
  have h1 : ∑ ψ : AddChar G ℂ, ψ a
      = ∑ ψ : AddChar G ℂ, (AddChar.doubleDualEmb a : AddChar (AddChar G ℂ) ℂ) ψ := rfl
  rw [h1, AddChar.sum_eq_zero_iff_ne_zero.mpr]
  exact AddChar.doubleDualEmb_ne_zero.mpr ha

private theorem sum_addChar_eq_ite {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (a : G) : ∑ ψ : AddChar G ℂ, ψ a
      = if a = 0 then (Fintype.card G : ℂ) else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [AddChar.card_eq]
  · rw [if_neg ha]
    exact sum_addChar_eq_zero a ha

/-- **Coefficient bound on a finite abelian amplifier group (Theorem 2.1, general finite
case).**  A symmetric real pattern whose real part is nonnegative at every character has
every coefficient bounded by the pole coefficient: dual averaging against the nonnegative
kernels `1 ± Re ψ(g₀)` isolates `c₀ ± c_{g₀} ≥ 0`.  The detection/pole ratio of every
finite abelian support is finite. -/
theorem finite_pattern_coeff_bound {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (c : G → ℝ) (hsym : ∀ g, c (-g) = c g)
    (hpos : ∀ ψ : AddChar G ℂ, 0 ≤ (∑ g, (c g : ℂ) * ψ g).re)
    (g₀ : G) : |c g₀| ≤ c 0 := by
  have hcardpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  set N : ℂ := (Fintype.card G : ℂ) with hN
  set Q : AddChar G ℂ → ℂ := fun ψ => ∑ g, (c g : ℂ) * ψ g with hQ
  -- the structured dual sum against one character value
  have hswap : ∀ h₀ : G, ∑ ψ : AddChar G ℂ, Q ψ * ψ h₀ = (c (-h₀) : ℂ) * N := by
    intro h₀
    have hexp : ∀ ψ : AddChar G ℂ, Q ψ * ψ h₀ = ∑ g, (c g : ℂ) * ψ g * ψ h₀ := by
      intro ψ
      rw [hQ]
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl fun ψ _ => hexp ψ, Finset.sum_comm]
    have hterm : ∀ g : G, ∑ ψ : AddChar G ℂ, (c g : ℂ) * ψ g * ψ h₀
        = if g = -h₀ then (c g : ℂ) * N else 0 := by
      intro g
      have h1 : ∑ ψ : AddChar G ℂ, (c g : ℂ) * ψ g * ψ h₀
          = (c g : ℂ) * ∑ ψ : AddChar G ℂ, ψ (g + h₀) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [AddChar.map_add_eq_mul]
        ring
      rw [h1, sum_addChar_eq_ite]
      by_cases hg : g = -h₀
      · rw [if_pos (by rw [hg]; simp), if_pos hg]
      · rw [if_neg (fun hc => hg (add_eq_zero_iff_eq_neg.mp hc)), if_neg hg]
        ring
    rw [Finset.sum_congr rfl fun g _ => hterm g,
      Finset.sum_ite_eq' Finset.univ (-h₀) (fun g => (c g : ℂ) * N),
      if_pos (Finset.mem_univ _)]
  -- the plain dual sum
  have hplain : ∑ ψ : AddChar G ℂ, Q ψ = (c 0 : ℂ) * N := by
    have h1 : ∀ ψ : AddChar G ℂ, Q ψ = Q ψ * ψ 0 := by
      intro ψ
      rw [AddChar.map_zero_eq_one, mul_one]
    rw [Finset.sum_congr rfl fun ψ _ => h1 ψ, hswap 0, neg_zero]
  -- real forms
  have hS0 : ∑ ψ : AddChar G ℂ, (Q ψ).re = c 0 * Fintype.card G := by
    rw [← Complex.re_sum, hplain, hN, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hkernel : ∀ ψ : AddChar G ℂ, ((ψ g₀).re : ℂ) = (ψ g₀ + ψ (-g₀)) / 2 := by
    intro ψ
    rw [AddChar.map_neg_eq_conj, Complex.add_conj]
    push_cast
    ring
  have hS1 : ∑ ψ : AddChar G ℂ, (Q ψ).re * (ψ g₀).re = c g₀ * Fintype.card G := by
    have hpt : ∀ ψ : AddChar G ℂ, (Q ψ).re * (ψ g₀).re
        = ((((ψ g₀).re : ℝ) : ℂ) * Q ψ).re := by
      intro ψ
      rw [Complex.re_ofReal_mul]
      ring
    have hsplit : ∀ ψ : AddChar G ℂ, ((((ψ g₀).re : ℝ) : ℂ) * Q ψ)
        = (Q ψ * ψ g₀ + Q ψ * ψ (-g₀)) / 2 := by
      intro ψ
      rw [hkernel ψ]
      ring
    have hsum : ∑ ψ : AddChar G ℂ, ((((ψ g₀).re : ℝ) : ℂ) * Q ψ)
        = ((c (-g₀) : ℂ) * N + (c (- -g₀) : ℂ) * N) / 2 := by
      rw [Finset.sum_congr rfl fun ψ _ => hsplit ψ, ← Finset.sum_div,
        Finset.sum_add_distrib, hswap g₀, hswap (-g₀)]
    have hval : ((c (-g₀) : ℂ) * N + (c (- -g₀) : ℂ) * N) / 2 = (c g₀ : ℂ) * N := by
      rw [neg_neg, hsym g₀]
      ring
    rw [Finset.sum_congr rfl fun ψ _ => hpt ψ, ← Complex.re_sum, hsum, hval, hN,
      ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  -- the two nonnegative kernel averages
  have hker : ∀ ψ : AddChar G ℂ, |(ψ g₀).re| ≤ 1 := by
    intro ψ
    calc |(ψ g₀).re| ≤ ‖ψ g₀‖ := Complex.abs_re_le_norm _
      _ = 1 := AddChar.norm_apply ψ g₀
  have hplus : 0 ≤ ∑ ψ : AddChar G ℂ, (Q ψ).re * (1 + (ψ g₀).re) := by
    refine Finset.sum_nonneg fun ψ _ => mul_nonneg (hpos ψ) ?_
    have := abs_le.mp (hker ψ)
    linarith [this.1]
  have hminus : 0 ≤ ∑ ψ : AddChar G ℂ, (Q ψ).re * (1 - (ψ g₀).re) := by
    refine Finset.sum_nonneg fun ψ _ => mul_nonneg (hpos ψ) ?_
    have := abs_le.mp (hker ψ)
    linarith [this.2]
  have hplusval : ∑ ψ : AddChar G ℂ, (Q ψ).re * (1 + (ψ g₀).re)
      = c 0 * Fintype.card G + c g₀ * Fintype.card G := by
    have : ∀ ψ : AddChar G ℂ, (Q ψ).re * (1 + (ψ g₀).re)
        = (Q ψ).re + (Q ψ).re * (ψ g₀).re := by
      intro ψ
      ring
    rw [Finset.sum_congr rfl fun ψ _ => this ψ, Finset.sum_add_distrib, hS0, hS1]
  have hminusval : ∑ ψ : AddChar G ℂ, (Q ψ).re * (1 - (ψ g₀).re)
      = c 0 * Fintype.card G - c g₀ * Fintype.card G := by
    have : ∀ ψ : AddChar G ℂ, (Q ψ).re * (1 - (ψ g₀).re)
        = (Q ψ).re - (Q ψ).re * (ψ g₀).re := by
      intro ψ
      ring
    rw [Finset.sum_congr rfl fun ψ _ => this ψ, Finset.sum_sub_distrib, hS0, hS1]
  rw [hplusval] at hplus
  rw [hminusval] at hminus
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end HTGeometry

namespace HTGeometry

open Finset

/-- **Coefficient bound through a separating finite quotient (Theorem 2.1, general
supports).**  For a finitely supported symmetric pattern on any abelian amplifier group,
nonnegativity at the characters pulled back from one finite quotient injective on the
support already bounds every coefficient by the pole coefficient.  Every finitely
generated support — in particular the mixed `ℤ^r × F` supports of the symmetric-power
anchors — admits such a quotient, so its detection/pole ratio is finite. -/
theorem pattern_coeff_bound_of_finite_quotient {Γ H : Type*} [AddCommGroup Γ]
    [DecidableEq Γ] [AddCommGroup H] [Fintype H] [DecidableEq H]
    (q : Γ →+ H) (S : Finset Γ) (hinj : Set.InjOn q (S : Set Γ))
    (h0S : (0 : Γ) ∈ S) (hsymS : ∀ g ∈ S, -g ∈ S)
    (c : Γ → ℝ) (hsupp : ∀ g ∉ S, c g = 0) (hsym : ∀ g, c (-g) = c g)
    (hpos : ∀ ψ : AddChar H ℂ, 0 ≤ (∑ g ∈ S, (c g : ℂ) * ψ (q g)).re)
    (g₀ : Γ) : |c g₀| ≤ c 0 := by
  classical
  set cH : H → ℝ := fun h => ∑ g ∈ S.filter (fun g' => q g' = h), c g with hcH
  have hfiber : ∀ g ∈ S, S.filter (fun g' => q g' = q g) = {g} := by
    intro g hg
    ext g'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hg', hq⟩
      exact hinj hg' hg hq
    · rintro rfl
      exact ⟨hg, rfl⟩
  have hcH_q : ∀ g ∈ S, cH (q g) = c g := by
    intro g hg
    rw [hcH]
    simp only
    rw [hfiber g hg, Finset.sum_singleton]
  have hcH_zero : cH 0 = c 0 := by
    have := hcH_q 0 h0S
    rw [map_zero] at this
    exact this
  have hcH_sym : ∀ h, cH (-h) = cH h := by
    intro h
    rw [hcH]
    simp only
    have himg : S.filter (fun g' => q g' = -h)
        = (S.filter (fun g' => q g' = h)).image (fun g => -g) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hgS, hq⟩
        exact ⟨-g, ⟨hsymS g hgS, by rw [map_neg, hq, neg_neg]⟩, neg_neg g⟩
      · rintro ⟨g', ⟨hg'S, hq'⟩, rfl⟩
        exact ⟨hsymS g' hg'S, by rw [map_neg, hq']⟩
    rw [himg, Finset.sum_image (fun a _ b _ hab => neg_injective hab)]
    exact Finset.sum_congr rfl fun g _ => hsym g
  have hQ : ∀ ψ : AddChar H ℂ, ∑ h : H, (cH h : ℂ) * ψ h
      = ∑ g ∈ S, (c g : ℂ) * ψ (q g) := by
    intro ψ
    have hexp : ∀ h : H, (cH h : ℂ) * ψ h
        = ∑ g ∈ S.filter (fun g' => q g' = h), (c g : ℂ) * ψ (q g) := by
      intro h
      rw [hcH]
      simp only
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [(Finset.mem_filter.mp hg).2]
    rw [Finset.sum_congr rfl fun h _ => hexp h]
    exact Finset.sum_fiberwise S (fun g => q g) (fun g => (c g : ℂ) * ψ (q g))
  have hpos' : ∀ ψ : AddChar H ℂ, 0 ≤ (∑ h : H, (cH h : ℂ) * ψ h).re := by
    intro ψ
    rw [hQ ψ]
    exact hpos ψ
  have hmain := finite_pattern_coeff_bound cH hcH_sym hpos'
  by_cases hg₀S : g₀ ∈ S
  · have := hmain (q g₀)
    rw [hcH_q g₀ hg₀S, hcH_zero] at this
    exact this
  · have h00 := hmain 0
    rw [hcH_zero] at h00
    have hc0 : 0 ≤ c 0 := le_trans (abs_nonneg _) h00
    rw [hsupp g₀ hg₀S, abs_zero]
    exact hc0

end HTGeometry

namespace HTGeometry

/-- Phase-shifted sampled cosine sum: a nontrivial frequency sum vanishes at every phase. -/
theorem cos_sample_sum_zero_phase (N : ℕ) (r : ℕ) (hr : 0 < r) (hrN : r < N) (φ : ℝ) :
    ∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * r * j / N + φ) = 0 := by
  have hsum := exp_unit_sum_zero N r hr hrN
  have hmul := congrArg (fun z => Complex.exp ((φ : ℝ) * Complex.I) * z) hsum
  simp only [mul_zero] at hmul
  rw [Finset.mul_sum] at hmul
  have := congrArg Complex.re hmul
  rw [Complex.re_sum] at this
  simp only [Complex.zero_re] at this
  calc ∑ j ∈ Finset.range N, Real.cos (2 * Real.pi * r * j / N + φ)
      = ∑ j ∈ Finset.range N,
          (Complex.exp ((φ : ℝ) * Complex.I)
            * Complex.exp (2 * Real.pi * Complex.I * r * j / N)).re := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Complex.exp_add]
        have harg : (φ : ℝ) * Complex.I + 2 * Real.pi * Complex.I * r * j / N
            = ((2 * Real.pi * r * j / N + φ : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [harg, Complex.exp_ofReal_mul_I_re]
    _ = 0 := this

end HTGeometry
