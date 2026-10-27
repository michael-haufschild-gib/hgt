import GaloisForLFunctions.BiarithmeticGaugeGeometry.RationalBochnerDeformationsOfTheHeightCoupledCarrier
import GaloisForLFunctions.MultiplicativePositivityGeometry.TotalZeroMass

/-!
# Anchor-Line Positivity and the Capacity of Rational Deformations

The Landau real anchor bounds each residue on the anchor line by the real one. This module proves the
full statement behind it: **the residue divisor of a positive exponential-cosine density on any
vertical line at or right of its weighted poles is an even positive-definite function of the
height**, and applies it to rational deformations of lattice positive systems.

1. **Line-residue positivity (`lineResidue_isEvenPosDef`).** If `w(t) = Σ c(z) e^{t Re z} cos(t Im z)`
   is nonnegative and `G = Σ c(z)/(s − z)` is conjugation symmetric, then for every finite family of
   heights and real coefficients, `∫ w(t) |Σ aₖ e^{iβₖ t}|² e^{−xt} dt = Σ aₖ aₗ Re G(x + i(βₖ − βₗ))`;
   multiplying by `x − σ` and letting `x ↓ σ` turns this into the Gram form of the line residues
   `b ↦ c(σ + ib)`.

2. **Rational deformations of lattice systems (`rationalDeformation_lattice_data`,
   `rationalDeformation_lineResidue_isEvenPosDef`).** For any base `F₀` whose `−F₀'/F₀` is a
   nonnegative Dirichlet series and any rational deformation `F = F₀ · ∏(s − zᵢ)^{mᵢ}` with even
   positive-definite sections, the divisor `b ↦ −M(σ + ib)` is even positive definite on every line
   `Re s = σ` bounding the multiplier points of nonzero net multiplicity.

3. **Critical-zero conservation in `HeightCoupledSystem 2 1 1 γ`
   (`rationalDeformation_critical_conservation`).** Without off-critical zeros at ordinate `γ`, a
   rational deformation that only creates zeros on the critical line creates at most half as many
   (upper half-plane, with multiplicity) as it removes from the centre:
   `2 Σ_{b > 0} M(1/2 + ib) ≤ −M(1/2) = ord_{1/2} Λ_γ − ord_{1/2} Λ`. The outward splitting `W_β`
   attains equality.

4. **Boundary capacity of completed positive systems
   (`rationalDeformation_zetaPow_boundary_capacity`, `rationalDeformation_zetaPow_rigid`).** A rational
   deformation of `ζ^d` inside `CompletedPositiveSystem κ d` has total boundary multiplicity
   `2 Σ_{β > 0} M(1 + iβ) ≤ κ − d`; if it has a boundary zero then `d < κ`. Hence the capacity
   `κ/2` is never attained by rational deformations of `ζ^d`, the boundary twist construction
   (`κ = d + 2r`, `r` boundary zeros) is optimal, and `ζ^d` is rationally rigid in
   `CompletedPositiveSystem d d`.
-/

open Complex Filter Topology Set MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry StripBochnerWeilForcing

/-! ## §1. Line-residue positivity of positive exponential-cosine densities -/

/-- Aggregated residue of the polar data at height `b` on the vertical line `Re s = σ`. -/
def lineResidue (S : Finset ℂ) (c : ℂ → ℝ) (σ b : ℝ) : ℝ :=
  ∑ z ∈ S, if z = (σ : ℂ) + (b : ℂ) * I then c z else 0

theorem lineResidue_eq (S : Finset ℂ) (c : ℂ → ℝ) (σ b : ℝ) :
    lineResidue S c σ b =
      if (σ : ℂ) + (b : ℂ) * I ∈ S then c ((σ : ℂ) + (b : ℂ) * I) else 0 := by
  classical
  exact Finset.sum_ite_eq' S _ _

/-- Residue extraction for the reflected sum `Σ c(z)/(s − conj z)`. -/
theorem tendsto_sub_mul_reflectedPolarSum (S : Finset ℂ) (c : ℂ → ℝ) (σ b : ℝ) :
    Tendsto (fun x : ℝ => ((x - σ : ℝ) : ℂ) *
        ∑ z ∈ S, (c z : ℂ) / ((x : ℂ) + (b : ℂ) * I - conj z)) (𝓝[>] σ)
      (𝓝 (∑ z ∈ S, if conj z = (σ : ℂ) + (b : ℂ) * I then (c z : ℂ) else 0)) := by
  simp_rw [Finset.mul_sum]
  refine tendsto_finsetSum _ fun z _ => ?_
  by_cases hz : conj z = (σ : ℂ) + (b : ℂ) * I
  · rw [if_pos hz]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : ((x - σ : ℝ) : ℂ) ≠ 0 := by
      have : x - σ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx); exact_mod_cast this
    rw [hz, show (x : ℂ) + (b : ℂ) * I - ((σ : ℂ) + (b : ℂ) * I) = ((x - σ : ℝ) : ℂ) by
      push_cast; ring]
    field_simp
  · rw [if_neg hz]
    have hden : (σ : ℂ) + (b : ℂ) * I - conj z ≠ 0 := fun h => hz (sub_eq_zero.mp h).symm
    have hcont : ContinuousAt (fun x : ℝ => ((x - σ : ℝ) : ℂ) *
        ((c z : ℂ) / ((x : ℂ) + (b : ℂ) * I - conj z))) σ := by
      refine ContinuousAt.mul (by fun_prop) (ContinuousAt.div continuousAt_const
        (by fun_prop) hden)
    have h := hcont.tendsto
    simp only [sub_self, Complex.ofReal_zero, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds

/-- Exponential bound `|w(t)| ≤ (Σ|c|) e^{σ t}` for weighted poles with `Re z ≤ σ`. -/
theorem abs_polarScaleWeight_le {S : Finset ℂ} {c : ℂ → ℝ} {σ : ℝ}
    (hσ : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σ) {t : ℝ} (ht : 0 ≤ t) :
    |polarScaleWeight S c t| ≤ (∑ z ∈ S, |c z|) * Real.exp (σ * t) := by
  unfold polarScaleWeight
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z hz => ?_)
  by_cases hcz : c z = 0
  · simp [hcz]
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (z.re * t) ≤ Real.exp (σ * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hσ z hz hcz) ht)
  have h2 := Real.abs_cos_le_one (z.im * t)
  calc |c z| * Real.exp (z.re * t) * |Real.cos (z.im * t)|
      ≤ |c z| * Real.exp (σ * t) * 1 := by gcongr
    _ = |c z| * Real.exp (σ * t) := mul_one _

theorem integrableOn_polarScaleWeight_mul_exp {S : Finset ℂ} {c : ℂ → ℝ} {σ : ℝ}
    (hσ : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σ) {x : ℝ} (hx : σ < x) (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hφb : ∀ t, |φ t| ≤ 1) :
    IntegrableOn (fun t => polarScaleWeight S c t * φ t * Real.exp (-x * t)) (Ioi 0) := by
  have hcont : Continuous (polarScaleWeight S c) := by unfold polarScaleWeight; fun_prop
  have hdom : IntegrableOn (fun t => (∑ z ∈ S, |c z|) * Real.exp ((σ - x) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine hdom.mono' ((hcont.mul hφ).mul (by fun_prop)).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |polarScaleWeight S c t| * |φ t| * Real.exp (-x * t)
      ≤ ((∑ z ∈ S, |c z|) * Real.exp (σ * t)) * 1 * Real.exp (-x * t) := by
        gcongr
        · exact abs_polarScaleWeight_le hσ ht'
        · exact hφb t
    _ = (∑ z ∈ S, |c z|) * Real.exp ((σ - x) * t) := by
        rw [mul_one, mul_assoc, ← Real.exp_add]; ring_nf

/-- `∫₀^∞ w(t) cos(βt) e^{−xt} dt = Re G(x + iβ)` for conjugation-symmetric polar data. -/
theorem integral_polarScaleWeight_cos_mul_exp {S : Finset ℂ} {c : ℂ → ℝ} {σ : ℝ}
    (hσ : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σ)
    (hsym : ∀ s : ℂ, σ < s.re → polarSum S c s = ∑ z ∈ S, (c z : ℂ) / (s - conj z))
    {x : ℝ} (hx : σ < x) (β : ℝ) :
    ∫ t in Ioi (0 : ℝ), polarScaleWeight S c t * Real.cos (β * t) * Real.exp (-x * t) =
      (polarSum S c ((x : ℂ) + (β : ℂ) * I)).re := by
  have hs : σ < ((x : ℂ) + (β : ℂ) * I).re := by simpa using hx
  have hrep : polarSum S c ((x : ℂ) + (β : ℂ) * I) =
      ∫ t in Ioi (0 : ℝ), (polarScaleWeight S c t : ℂ) *
        cexp (-((x : ℂ) + (β : ℂ) * I) * t) := by
    rw [integral_polarScaleWeight_mul_exp hσ hs, ← hsym _ hs]
    ring
  have hint : Integrable (fun t : ℝ => (polarScaleWeight S c t : ℂ) *
      cexp (-((x : ℂ) + (β : ℂ) * I) * t)) (volume.restrict (Ioi 0)) := by
    have hreal := integrableOn_polarScaleWeight_mul_exp hσ hx (fun _ => 1) continuous_const
      (fun _ => by simp)
    refine Integrable.mono' hreal.norm ?_ ?_
    · have hcont : Continuous (polarScaleWeight S c) := by unfold polarScaleWeight; fun_prop
      exact (by fun_prop : Continuous fun t : ℝ => (polarScaleWeight S c t : ℂ) *
        cexp (-((x : ℂ) + (β : ℂ) * I) * t)).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      rw [norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_eq_abs, Real.norm_eq_abs,
        mul_one, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply le_of_eq
      congr 2
      simp [Complex.mul_re]
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [hrep, ← hre]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [show -((x : ℂ) + (β : ℂ) * I) * (t : ℂ) = ((-x * t : ℝ) : ℂ) + ((-β * t : ℝ) : ℂ) * I by
    push_cast; ring, Complex.re_ofReal_mul, Complex.exp_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, add_zero]
  rw [show -β * t = -(β * t) by ring, Real.cos_neg]
  ring

/-- **Line-residue positivity.** For conjugation-symmetric polar data with a nonnegative scale
weight, the residue divisor `b ↦ c(σ + ib)` on any line `Re s = σ` bounding the weighted poles is an
even positive-definite function on `ℝ`. -/
theorem lineResidue_isEvenPosDef {S : Finset ℂ} {c : ℂ → ℝ} {σ : ℝ}
    (hσ : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σ)
    (hsym : ∀ s : ℂ, σ < s.re → polarSum S c s = ∑ z ∈ S, (c z : ℂ) / (s - conj z))
    (hw : ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t) :
    IsEvenPosDef (lineResidue S c σ) := by
  classical
  have hres : ∀ b : ℝ, Tendsto (fun x : ℝ => ((x - σ : ℝ) : ℂ) *
      polarSum S c ((x : ℂ) + (b : ℂ) * I)) (𝓝[>] σ) (𝓝 (lineResidue S c σ b : ℂ)) := by
    intro b
    have h := tendsto_sub_mul_polarSum S c σ b
    convert h using 2
    unfold lineResidue
    push_cast
    exact Finset.sum_congr rfl fun z _ => by split_ifs <;> simp
  refine ⟨fun b => ?_, fun n x a => ?_⟩
  · -- evenness: the residue of `G` at `σ − ib` is the residue of the reflected sum at `σ + ib`
    have h1 := tendsto_sub_mul_reflectedPolarSum S c σ b
    have h2 := hres b
    have heq : ∀ᶠ y in 𝓝[>] σ, ((y - σ : ℝ) : ℂ) * polarSum S c ((y : ℂ) + (b : ℂ) * I) =
        ((y - σ : ℝ) : ℂ) * ∑ z ∈ S, (c z : ℂ) / ((y : ℂ) + (b : ℂ) * I - conj z) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [hsym _ (by simpa using hy)]
    have hlim := tendsto_nhds_unique (h2.congr' heq) h1
    have hrefl : (∑ z ∈ S, if conj z = (σ : ℂ) + (b : ℂ) * I then (c z : ℂ) else 0) =
        (lineResidue S c σ (-b) : ℂ) := by
      unfold lineResidue
      push_cast
      refine Finset.sum_congr rfl fun z _ => ?_
      have hiff : conj z = (σ : ℂ) + (b : ℂ) * I ↔ z = (σ : ℂ) + -(b : ℂ) * I := by
        constructor
        · intro h; rw [← Complex.conj_conj z, h]; apply Complex.ext <;> simp
        · intro h; rw [h]; apply Complex.ext <;> simp
      by_cases hz : conj z = (σ : ℂ) + (b : ℂ) * I
      · rw [if_pos hz, if_pos (hiff.mp hz)]
      · rw [if_neg hz, if_neg (fun h => hz (hiff.mpr h)), Complex.ofReal_zero]
    rw [hrefl] at hlim
    exact_mod_cast hlim.symm
  · -- Gram form through the Laplace transform of `w · |Σ aₖ e^{iβₖ t}|²`
    set Q : ℝ → ℝ := fun t => ∑ i, ∑ j, a i * a j * Real.cos ((x i - x j) * t) with hQ
    have hQnn : ∀ t, 0 ≤ Q t := by
      intro t
      have hsq : Q t = (∑ i, a i * Real.cos (x i * t)) ^ 2 + (∑ i, a i * Real.sin (x i * t)) ^ 2 := by
        simp only [hQ, sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [sub_mul, Real.cos_sub]; ring
      rw [hsq]; positivity
    have hlap : ∀ y : ℝ, σ < y →
        ∫ t in Ioi (0 : ℝ), polarScaleWeight S c t * Q t * Real.exp (-y * t) =
          ∑ i, ∑ j, a i * a j * (polarSum S c ((y : ℂ) + ((x i - x j : ℝ) : ℂ) * I)).re := by
      intro y hy
      have hint : ∀ i j, IntegrableOn (fun t => a i * a j *
          (polarScaleWeight S c t * Real.cos ((x i - x j) * t) * Real.exp (-y * t))) (Ioi 0) :=
        fun i j => (integrableOn_polarScaleWeight_mul_exp hσ hy _ (by fun_prop)
          (fun t => Real.abs_cos_le_one _)).const_mul _
      have hexp : ∀ t, polarScaleWeight S c t * Q t * Real.exp (-y * t) =
          ∑ i, ∑ j, a i * a j *
            (polarScaleWeight S c t * Real.cos ((x i - x j) * t) * Real.exp (-y * t)) := by
        intro t
        simp only [hQ, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hexp]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hint i j]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_polarScaleWeight_cos_mul_exp hσ hsym hy]
    have hnn : ∀ y : ℝ, σ < y →
        0 ≤ ∑ i, ∑ j, a i * a j * (polarSum S c ((y : ℂ) + ((x i - x j : ℝ) : ℂ) * I)).re := by
      intro y hy
      rw [← hlap y hy]
      refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
      exact mul_nonneg (mul_nonneg (hw t ht) (hQnn t)) (Real.exp_pos _).le
    have hlim : Tendsto (fun y : ℝ => ∑ i, ∑ j, a i * a j *
        (((y - σ : ℝ) : ℂ) * polarSum S c ((y : ℂ) + ((x i - x j : ℝ) : ℂ) * I)).re)
        (𝓝[>] σ) (𝓝 (∑ i, ∑ j, a i * a j * lineResidue S c σ (x i - x j))) := by
      refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
      have h := (Complex.continuous_re.tendsto _).comp (hres (x i - x j))
      simpa using h.const_mul (a i * a j)
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : σ < y := hy
    have hpos : 0 ≤ y - σ := (sub_pos.mpr hy').le
    have heq : ∑ i, ∑ j, a i * a j *
        (((y - σ : ℝ) : ℂ) * polarSum S c ((y : ℂ) + ((x i - x j : ℝ) : ℂ) * I)).re =
        (y - σ) * ∑ i, ∑ j, a i * a j *
          (polarSum S c ((y : ℂ) + ((x i - x j : ℝ) : ℂ) * I)).re := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.re_ofReal_mul]; ring
    rw [heq]
    exact mul_nonneg hpos (hnn y hy')

/-! ## §2. Rational deformations of lattice positive systems -/

/-- Real parts of the polar sum are even on vertical lines when the lattice-plus-polar sections are
even (a real Dirichlet series is conjugation equivariant). -/
theorem polarSum_re_even_of_lattice_even {b : ℕ → ℝ} {S : Finset ℂ} {c : ℂ → ℝ} {a : ℝ}
    (hpd : ∀ σ : ℝ, a < σ → IsEvenPosDef fun u : ℝ =>
      (LSeries (fun n => (b n : ℂ)) ((σ : ℂ) + (u : ℂ) * I) +
        polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re) :
    ∀ σ' : ℝ, a < σ' → ∀ u : ℝ,
      (polarSum S c ((σ' : ℂ) + ((-u : ℝ) : ℂ) * I)).re =
        (polarSum S c ((σ' : ℂ) + (u : ℂ) * I)).re := by
  intro σ' hσ' u
  have h := (hpd σ' hσ').even u
  have hc : (σ' : ℂ) + ((-u : ℝ) : ℂ) * I = conj ((σ' : ℂ) + (u : ℂ) * I) := by
    apply Complex.ext <;> simp
  simp only [Complex.add_re] at h
  rw [hc, LSeries_ofReal_conj, Complex.conj_re] at h
  rw [hc]
  linarith

/-- **Lattice line-residue positivity.** For a nonnegative lattice series plus a finite polar sum
with even positive-definite sections on `σ > a`, the residue divisor on any line bounding the
weighted poles is even positive definite. -/
theorem lattice_lineResidue_isEvenPosDef {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    {S : Finset ℂ} {c : ℂ → ℝ} {a : ℝ} (hSa : ∀ z ∈ S, z.re ≤ a)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) < a)
    (hpd : ∀ σ : ℝ, a < σ → IsEvenPosDef fun u : ℝ =>
      (LSeries (fun n => (b n : ℂ)) ((σ : ℂ) + (u : ℂ) * I) +
        polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    {σ : ℝ} (hσ : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σ) :
    IsEvenPosDef (lineResidue S c σ) :=
  lineResidue_isEvenPosDef hσ
    (fun _ hs => polarSum_eq_reflected_of_even hSa hσ (polarSum_re_even_of_lattice_even hpd) hs)
    (fun _ ht => polarScaleWeight_nonneg_of_lattice_posDef hb hSa habs
      (fun σ' hσ' => (hpd σ' hσ').posDef) ht)

theorem exists_bound_re_rationalMultiplier {n : ℕ} (z : Fin n → ℂ) :
    ∃ a : ℝ, 1 < a ∧ ∀ i, (z i).re + 1 < a := by
  refine ⟨2 + ∑ i, |(z i).re|, ?_, fun i => ?_⟩
  · have : 0 ≤ ∑ i, |(z i).re| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  · have h1 := Finset.single_le_sum (f := fun i => |(z i).re|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    have h2 := le_abs_self (z i).re
    linarith

/-- **Lattice data of a rational deformation.** If `−F₀'/F₀` is a nonnegative Dirichlet series on
`Re s > 1` and `F = F₀ · R` has even positive-definite sections, then to the right of the multiplier
points `−F'/F` is the lattice series plus the polar sum of `R`, with even positive-definite sections. -/
theorem rationalDeformation_lattice_data {b : ℕ → ℝ}
    (habs1 : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    {F₀ F : ℂ → ℂ} (hF₀d : DifferentiableOn ℂ F₀ {s : ℂ | 1 < s.re})
    (hF₀nz : ∀ s : ℂ, 1 < s.re → F₀ s ≠ 0)
    (hF₀L : ∀ s : ℂ, 1 < s.re → -logDeriv F₀ s = LSeries (fun n => (b n : ℂ)) s)
    (hpos : ∀ {σ : ℝ}, 1 < σ →
      IsEvenPosDef fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re)
    {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = F₀ s * rationalMultiplier z m s) :
    ∃ a : ℝ, (∀ w ∈ Finset.univ.image z, w.re ≤ a) ∧
      LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) < a ∧
      ∀ σ : ℝ, a < σ → IsEvenPosDef fun u : ℝ =>
        (LSeries (fun n => (b n : ℂ)) ((σ : ℂ) + (u : ℂ) * I) +
          polarSum (Finset.univ.image z) (multiplierWeight z m) ((σ : ℂ) + (u : ℂ) * I)).re := by
  obtain ⟨a, ha1, hza⟩ := exists_bound_re_rationalMultiplier z
  refine ⟨a, fun w hw => ?_, lt_of_le_of_lt habs1 (by exact_mod_cast ha1), fun σ hσ => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    linarith [hza i]
  have hsplit : ∀ s : ℂ, a < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s +
      polarSum (Finset.univ.image z) (multiplierWeight z m) s := by
    intro s hs
    have hs1 : 1 < s.re := by linarith
    have hsz : ∀ i, s ≠ z i := fun i h => by have := hza i; rw [← h] at this; linarith
    have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : F =ᶠ[𝓝 s] fun w => F₀ w * rationalMultiplier z m w :=
      Filter.eventually_of_mem (hU.mem_nhds hs1) fun w hw => hF w hw
    have hlogF : logDeriv F s = logDeriv (fun w => F₀ w * rationalMultiplier z m w) s := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
    have hR_ne : rationalMultiplier z m s ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (sub_ne_zero.mpr (hsz i))
    rw [hlogF, logDeriv_mul s (hF₀nz s hs1) hR_ne
      ((hF₀d s hs1).differentiableAt (hU.mem_nhds hs1))
      (rationalMultiplier_analyticAt z m hsz).differentiableAt, neg_add, hF₀L s hs1,
      neg_logDeriv_rationalMultiplier z m hsz]
  have h := hpos (σ := σ) (by linarith)
  have heq : (fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re) =
      fun u : ℝ => (LSeries (fun n => (b n : ℂ)) ((σ : ℂ) + (u : ℂ) * I) +
        polarSum (Finset.univ.image z) (multiplierWeight z m) ((σ : ℂ) + (u : ℂ) * I)).re := by
    funext u; rw [hsplit _ (by simpa using hσ)]
  rwa [heq] at h

/-- **Anchor-line positivity for rational deformations.** For a rational deformation `F = F₀ · R` of
a nonnegative lattice base with even positive-definite sections, the divisor `β ↦ −M(σ + iβ)` is even
positive definite on every line `Re s = σ` bounding the points of nonzero net multiplicity. -/
theorem rationalDeformation_lineResidue_isEvenPosDef {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs1 : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    {F₀ F : ℂ → ℂ} (hF₀d : DifferentiableOn ℂ F₀ {s : ℂ | 1 < s.re})
    (hF₀nz : ∀ s : ℂ, 1 < s.re → F₀ s ≠ 0)
    (hF₀L : ∀ s : ℂ, 1 < s.re → -logDeriv F₀ s = LSeries (fun n => (b n : ℂ)) s)
    (hpos : ∀ {σ : ℝ}, 1 < σ →
      IsEvenPosDef fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re)
    {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = F₀ s * rationalMultiplier z m s)
    {σ : ℝ} (hσ : ∀ w : ℂ, netMultiplicity z m w ≠ 0 → w.re ≤ σ) :
    IsEvenPosDef fun β : ℝ => -(netMultiplicity z m ((σ : ℂ) + (β : ℂ) * I) : ℝ) := by
  obtain ⟨a, hSa, habs, hpd⟩ :=
    rationalDeformation_lattice_data habs1 hF₀d hF₀nz hF₀L hpos hF
  have h := lattice_lineResidue_isEvenPosDef hb hSa habs hpd (σ := σ)
    (fun w _ hw => hσ w (by simpa [multiplierWeight] using hw))
  have heq : lineResidue (Finset.univ.image z) (multiplierWeight z m) σ =
      fun β : ℝ => -(netMultiplicity z m ((σ : ℂ) + (β : ℂ) * I) : ℝ) := by
    funext β
    rw [lineResidue_eq]
    split_ifs with hβ
    · rfl
    · rw [netMultiplicity_eq_zero_of_notMem z m hβ]; simp
  rwa [heq] at h

/-- The real anchor for rational deformations of a general lattice base. -/
theorem rationalDeformation_anchor {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs1 : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    {F₀ F : ℂ → ℂ} (hF₀d : DifferentiableOn ℂ F₀ {s : ℂ | 1 < s.re})
    (hF₀nz : ∀ s : ℂ, 1 < s.re → F₀ s ≠ 0)
    (hF₀L : ∀ s : ℂ, 1 < s.re → -logDeriv F₀ s = LSeries (fun n => (b n : ℂ)) s)
    (hpos : ∀ {σ : ℝ}, 1 < σ →
      IsEvenPosDef fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re)
    {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = F₀ s * rationalMultiplier z m s)
    {w₀ : ℂ} (hw₀ : netMultiplicity z m w₀ ≠ 0)
    (htop : ∀ w : ℂ, netMultiplicity z m w ≠ 0 → w.re ≤ w₀.re) :
    netMultiplicity z m (w₀.re : ℂ) < 0 := by
  obtain ⟨a, hSa, habs, hpd⟩ :=
    rationalDeformation_lattice_data habs1 hF₀d hF₀nz hF₀L hpos hF
  have hw₀S : w₀ ∈ Finset.univ.image z := by
    by_contra h; exact hw₀ (netMultiplicity_eq_zero_of_notMem z m h)
  obtain ⟨_, hpos', -⟩ := lattice_real_anchor hb hSa habs hpd hw₀S
    (by simp [multiplierWeight, hw₀]) (fun w _ hw => htop w (by simpa [multiplierWeight] using hw))
  have : ((netMultiplicity z m (w₀.re : ℂ) : ℤ) : ℝ) < 0 := by
    simpa [multiplierWeight] using hpos'
  exact_mod_cast this

/-! ## §3. The local order law and the identity theorem off the multiplier -/

theorem eventually_ne_multiplierPoints {n : ℕ} (z : Fin n → ℂ) (x : ℂ) :
    ∀ᶠ s in 𝓝[≠] x, ∀ i, s ≠ z i := by
  refine Filter.eventually_all.mpr fun i => ?_
  by_cases hi : z i = x
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hi]; exact hs
  · exact nhdsWithin_le_nhds (eventually_ne_nhds (Ne.symm hi))

/-- **Local order law.** If `Λ = Λ' · R` off the multiplier points with `Λ, Λ'` entire, then at every
point `ord_w Λ + M(w)⁻ = ord_w Λ' + M(w)⁺`. -/
theorem analyticOrderAt_add_eq_of_eq_mul_rationalMultiplier {n : ℕ} {z : Fin n → ℂ}
    {m : Fin n → ℤ} {Λ Λ' : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) (hΛ' : Differentiable ℂ Λ')
    (heq : ∀ s : ℂ, (∀ i, s ≠ z i) → Λ s = Λ' s * rationalMultiplier z m s) (w : ℂ) :
    analyticOrderAt Λ w + ((-netMultiplicity z m w).toNat : ℕ∞) =
      analyticOrderAt Λ' w + ((netMultiplicity z m w).toNat : ℕ∞) := by
  set M := netMultiplicity z m w with hMdef
  set k₁ : ℕ := (-M).toNat
  set k₂ : ℕ := M.toNat
  have hM : M = (k₂ : ℤ) - (k₁ : ℤ) := by
    simp only [k₁, k₂]; omega
  have hpunct : ∀ᶠ s in 𝓝[≠] w,
      Λ s * (s - w) ^ k₁ = Λ' s * multiplierCofactor z m w s * (s - w) ^ k₂ := by
    filter_upwards [eventually_ne_multiplierPoints z w, self_mem_nhdsWithin] with s hs hsw
    have hsw' : s - w ≠ 0 := sub_ne_zero.mpr hsw
    rw [heq s hs, rationalMultiplier_eq_zpow_mul_cofactor z m hsw, ← hMdef, hM,
      zpow_sub₀ hsw', zpow_natCast, zpow_natCast]
    field_simp
  have hcL : Continuous fun s : ℂ => Λ s * (s - w) ^ k₁ := hΛ.continuous.mul (by fun_prop)
  have hcR : ContinuousAt (fun s : ℂ => Λ' s * multiplierCofactor z m w s * (s - w) ^ k₂) w :=
    (hΛ'.continuous.continuousAt.mul (multiplierCofactor_analyticAt z m w).continuousAt).mul
      (by fun_prop)
  have hat := tendsto_nhds_unique ((hcL.tendsto _).mono_left nhdsWithin_le_nhds)
    ((hcR.tendsto.mono_left nhdsWithin_le_nhds).congr' (hpunct.mono fun s hs => hs.symm))
  have hfull : (fun s : ℂ => Λ s * (s - w) ^ k₁) =ᶠ[𝓝 w]
      fun s => Λ' s * multiplierCofactor z m w s * (s - w) ^ k₂ := by
    filter_upwards [eventually_nhdsWithin_iff.mp hpunct] with s hs
    by_cases hsw : s = w
    · rw [hsw]; exact hat
    · exact hs hsw
  have hg₁ : AnalyticAt ℂ (fun s : ℂ => (s - w) ^ k₁) w :=
    (analyticAt_id.sub analyticAt_const).pow k₁
  have hg₂ : AnalyticAt ℂ (fun s : ℂ => (s - w) ^ k₂) w :=
    (analyticAt_id.sub analyticAt_const).pow k₂
  have hR := multiplierCofactor_analyticAt z m w
  have hordL : analyticOrderAt (fun s : ℂ => Λ s * (s - w) ^ k₁) w =
      analyticOrderAt Λ w + k₁ := by
    rw [show (fun s : ℂ => Λ s * (s - w) ^ k₁) = Λ * fun s : ℂ => (s - w) ^ k₁ from rfl,
      analyticOrderAt_mul (hΛ.analyticAt w) hg₁, analyticOrderAt_sub_pow]
  have hordR : analyticOrderAt (fun s : ℂ => Λ' s * multiplierCofactor z m w s * (s - w) ^ k₂) w =
      analyticOrderAt Λ' w + k₂ := by
    rw [show (fun s : ℂ => Λ' s * multiplierCofactor z m w s * (s - w) ^ k₂) =
        Λ' * multiplierCofactor z m w * fun s : ℂ => (s - w) ^ k₂ from rfl,
      analyticOrderAt_mul ((hΛ'.analyticAt w).mul hR) hg₂,
      analyticOrderAt_mul (hΛ'.analyticAt w) hR,
      hR.analyticOrderAt_eq_zero.mpr (multiplierCofactor_self_ne_zero z m w), add_zero,
      analyticOrderAt_sub_pow]
  have h := analyticOrderAt_congr hfull
  rwa [hordL, hordR] at h

/-- Identity theorem off the multiplier: agreement right of the multiplier points propagates to the
connected complement of the finite multiplier set. -/
theorem eq_mul_rationalMultiplier_of_agree {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    {Λ Λ' : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) (hΛ' : Differentiable ℂ Λ') {a : ℝ}
    (hza : ∀ i, (z i).re < a)
    (hagree : ∀ s : ℂ, a < s.re → Λ s = Λ' s * rationalMultiplier z m s)
    {s : ℂ} (hs : ∀ i, s ≠ z i) : Λ s = Λ' s * rationalMultiplier z m s := by
  set V : Set ℂ := (Set.range z)ᶜ
  have hVconn : IsPreconnected V :=
    ((Set.finite_range z).countable.isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected
  have hmemV : ∀ x : ℂ, (∀ i, x ≠ z i) → x ∈ V := fun x hx ⟨i, hi⟩ => hx i hi.symm
  have hAΛ : AnalyticOnNhd ℂ Λ V := fun x _ => hΛ.analyticAt x
  have hAR : AnalyticOnNhd ℂ (fun x => Λ' x * rationalMultiplier z m x) V := fun x hx =>
    (hΛ'.analyticAt x).mul (rationalMultiplier_analyticAt z m fun i h => hx ⟨i, h.symm⟩)
  have hU : IsOpen {x : ℂ | a < x.re} := isOpen_lt continuous_const Complex.continuous_re
  set p : ℂ := ((a + 1 : ℝ) : ℂ)
  have hpU : p ∈ {x : ℂ | a < x.re} := by simp [p]
  have hpV : p ∈ V := hmemV p fun i h => by
    have := congrArg Complex.re h; simp [p] at this; linarith [hza i]
  have hev : Λ =ᶠ[𝓝 p] fun x => Λ' x * rationalMultiplier z m x :=
    Filter.eventually_of_mem (hU.mem_nhds hpU) fun x hx => hagree x hx
  exact hAΛ.eqOn_of_preconnected_of_eventuallyEq hAR hVconn hpV hev (hmemV s hs)

/-! ## §4. Critical-zero conservation in `HeightCoupledSystem 2 1 1 γ` -/

/-- **The critical-line divisor of a rational deformation is positive definite.** Without
off-critical zeros of `ξ` at ordinate `γ`, the divisor `β ↦ −M(1/2 + iβ)` of every rational
deformation of `ζ_γ` is an even positive-definite function. -/
theorem rationalDeformation_criticalLine_isEvenPosDef {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta γ s * rationalMultiplier z m s) :
    IsEvenPosDef fun β : ℝ => -(netMultiplicity z m (((1 / 2 : ℝ) : ℂ) + (β : ℂ) * I) : ℝ) := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  have hσ : ∀ w : ℂ, netMultiplicity z m w ≠ 0 → w.re ≤ 1 / 2 := by
    intro w hw
    obtain ⟨w₀, hw₀, htop⟩ := exists_top_netMultiplicity hw
    have hxi := (rationalDeformation_real_anchor hHC hF hw₀ htop).2.2
    rw [← hoff _ hxi]
    exact htop w hw
  exact rationalDeformation_lineResidue_isEvenPosDef (heightCoupledVonMangoldt_nonneg γ)
    (abscissaOfAbsConv_heightCoupledVonMangoldt_le_one γ) hHC0.diffOn_F hHC0.ne_zero_F
    (fun s hs => neg_logDeriv_heightCoupledF_eq_LSeries γ hs) hHC.posDef_neg_logDeriv hF hσ

/-- **Critical-zero conservation.** Without off-critical zeros of `ξ` at ordinate `γ`, a rational
deformation of `ζ_γ` that creates zeros only (no removal off the centre) on the critical line obeys
`2 Σ_{β ∈ Z} M(1/2 + iβ) + ord_{1/2} Λ ≤ ord_{1/2} Λ_γ` for every finite set `Z` of positive
heights: each upper-half critical zero created costs two orders of central vanishing. The outward
splitting `W_β` attains equality. -/
theorem rationalDeformation_critical_conservation {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = heightCoupledF riemannZeta γ s * rationalMultiplier z m s)
    (hcreate : ∀ β : ℝ, β ≠ 0 → 0 ≤ netMultiplicity z m (((1 / 2 : ℝ) : ℂ) + (β : ℂ) * I))
    {Z : Finset ℝ} (hZ : ∀ β ∈ Z, 0 < β) :
    2 * ∑ β ∈ Z, netMultiplicity z m (((1 / 2 : ℝ) : ℂ) + (β : ℂ) * I) +
        ((analyticOrderAt Λ (1 / 2)).toNat : ℤ) ≤
      ((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat : ℤ) := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set M := netMultiplicity z m
  have hD := rationalDeformation_criticalLine_isEvenPosDef hoff hHC hF
  have hcap := total_zero_mass_le hD (fun β hβ => by
    have := hcreate β hβ; simp only [neg_nonpos]; exact_mod_cast this) hZ
  have hD0 := hD.apply_zero_nonneg
  simp only [neg_neg, Complex.ofReal_zero, zero_mul, add_zero] at hcap hD0
  have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf] at hcap hD0
  have hM0 : M (1 / 2) ≤ 0 := by
    have : ((M (1 / 2) : ℤ) : ℝ) ≤ 0 := by linarith
    exact_mod_cast this
  have hcapZ : 2 * ∑ β ∈ Z, M (((1 / 2 : ℝ) : ℂ) + (β : ℂ) * I) ≤ -M (1 / 2) := by
    have : (2 : ℝ) * ∑ β ∈ Z, ((M (((1 / 2 : ℝ) : ℂ) + (β : ℂ) * I) : ℤ) : ℝ) ≤
        -((M (1 / 2) : ℤ) : ℝ) := by
      have h := hcap
      push_cast at h ⊢
      linarith
    exact_mod_cast this
  have hord := analyticOrderAt_add_eq_of_eq_mul_rationalMultiplier hHC.entire_Λ hHC0.entire_Λ
    (fun s hs => completion_eq_mul_rationalMultiplier hHC hF hs) (1 / 2)
  have hk₂ : (M (1 / 2)).toNat = 0 := by omega
  rw [hk₂, Nat.cast_zero, add_zero] at hord
  obtain ⟨b₀, hb₀⟩ := ENat.ne_top_iff_exists.mp (hHC0.orderAt_ne_top (1 / 2))
  obtain ⟨a₀, ha₀⟩ := ENat.ne_top_iff_exists.mp (hHC.orderAt_ne_top (1 / 2))
  rw [← hb₀, ← ha₀] at hord ⊢
  rw [ENat.toNat_coe, ENat.toNat_coe]
  have hnat : a₀ + (-M (1 / 2)).toNat = b₀ := by exact_mod_cast hord
  have hk₁ : (((-M (1 / 2)).toNat : ℕ) : ℤ) = -M (1 / 2) := Int.toNat_of_nonneg (by omega)
  omega

/-! ## §5. Boundary capacity of completed positive systems over `ζ^d` -/

/-- Lattice coefficients `d · Λ(n)` of `−(ζ^d)'/ζ^d`. -/
theorem neg_logDeriv_zeta_pow_eq_LSeries (d : ℕ) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (fun w => riemannZeta w ^ d) s =
      LSeries (fun n => ((d * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
  have hne : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  rw [logDeriv_fun_pow (differentiableAt_riemannZeta hne), logDeriv_apply,
    show (fun n => ((d * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) =
      (d : ℂ) • fun n => (ArithmeticFunction.vonMangoldt n : ℂ) by
      funext n; simp [Pi.smul_apply], LSeries_smul,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div]
  ring

theorem abscissaOfAbsConv_zeta_pow_le_one (d : ℕ) :
    LSeries.abscissaOfAbsConv (fun n => ((d * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (y : ℂ)) (by simpa using hy)
  refine Summable.of_norm_bounded (hΛ.norm.mul_left (d : ℝ)) fun n => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs with hn
  · simp
  · refine le_of_eq ?_
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      Nat.abs_cast, mul_div_assoc]

/-- Completion identity for rational deformations of `ζ^d` in `CompletedPositiveSystem κ d`:
`Λ (s(s−1))^{d−κ} = (s(s−1))^{κ−d} (2ξ)^d · R` off the multiplier points. -/
theorem zetaPow_completion_eq {κ d : ℕ} {F Λ : ℂ → ℂ} (hS : CompletedPositiveSystem κ d F Λ)
    {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = riemannZeta s ^ d * rationalMultiplier z m s)
    {s : ℂ} (hs : ∀ i, s ≠ z i) :
    Λ s * (s * (s - 1)) ^ (d - κ) =
      (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d * rationalMultiplier z m s := by
  have hZ := completedPositiveSystem_riemannZeta
  obtain ⟨a, ha1, hza⟩ := exists_bound_re_rationalMultiplier z
  refine eq_mul_rationalMultiplier_of_agree (Λ := fun s => Λ s * (s * (s - 1)) ^ (d - κ))
    (Λ' := fun s => (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d)
    (hS.entire_Λ.mul (by fun_prop)) ((by fun_prop : Differentiable ℂ
      fun s : ℂ => (s * (s - 1)) ^ (κ - d)).mul (hZ.entire_Λ.pow d))
    (a := a) (fun i => by linarith [hza i]) (fun x hx => ?_) hs
  have hx1 : 1 < x.re := by linarith
  have hξ : 2 * RHTower.xi x = x * (x - 1) * Complex.Gammaℝ x * riemannZeta x := by
    simpa using hZ.completed_eq x hx1
  rw [hS.completed_eq x hx1, hF x hx1, hξ]
  have hpow : (x * (x - 1)) ^ κ * (x * (x - 1)) ^ (d - κ) =
      (x * (x - 1)) ^ (κ - d) * (x * (x - 1)) ^ d := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  calc (x * (x - 1)) ^ κ * Complex.Gammaℝ x ^ d * (riemannZeta x ^ d * rationalMultiplier z m x) *
        (x * (x - 1)) ^ (d - κ)
      = ((x * (x - 1)) ^ κ * (x * (x - 1)) ^ (d - κ)) * Complex.Gammaℝ x ^ d *
          riemannZeta x ^ d * rationalMultiplier z m x := by ring
    _ = (x * (x - 1)) ^ (κ - d) * (x * (x - 1) * Complex.Gammaℝ x * riemannZeta x) ^ d *
          rationalMultiplier z m x := by rw [hpow]; simp only [mul_pow]; ring

theorem zetaPow_base_differentiable (κ d : ℕ) :
    Differentiable ℂ fun s : ℂ => (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d :=
  (by fun_prop : Differentiable ℂ fun s : ℂ => (s * (s - 1)) ^ (κ - d)).mul
    (completedPositiveSystem_riemannZeta.entire_Λ.pow d)

/-- The base completion `(s(s−1))^{κ−d} (2ξ)^d` vanishes at a real point only at `0, 1`, and only
when `d < κ`. -/
theorem zetaPow_base_real_zero {κ d : ℕ} {x : ℝ}
    (h : ((x : ℂ) * ((x : ℂ) - 1)) ^ (κ - d) * (2 * RHTower.xi x) ^ d = 0) :
    d < κ ∧ (x = 0 ∨ x = 1) := by
  rcases mul_eq_zero.mp h with h1 | h2
  · have hk : κ - d ≠ 0 := fun hk => by rw [hk, pow_zero] at h1; exact one_ne_zero h1
    have h1' := pow_eq_zero_iff hk |>.mp h1
    refine ⟨by omega, ?_⟩
    rcases mul_eq_zero.mp h1' with h | h
    · left; exact_mod_cast h
    · right; have : (x : ℂ) = 1 := sub_eq_zero.mp h; exact_mod_cast this
  · exfalso
    have hd : d ≠ 0 := by rintro rfl; simp at h2
    have h2' := (pow_eq_zero_iff hd).mp h2
    exact RHTower.xi_ne_zero_of_real x ((mul_eq_zero.mp h2').resolve_left two_ne_zero)

/-- **Rational rigidity of `ζ^d` without pole budget.** If `κ ≤ d`, every rational deformation of
`ζ^d` in `CompletedPositiveSystem κ d` is trivial: `κ = d` and `F = ζ^d` on `Re s > 1`. -/
theorem rationalDeformation_zetaPow_rigid {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) (hκ : κ ≤ d) {n : ℕ} {z : Fin n → ℂ}
    {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = riemannZeta s ^ d * rationalMultiplier z m s) :
    κ = d ∧ ∀ s : ℂ, 1 < s.re → F s = riemannZeta s ^ d := by
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hzd : DifferentiableOn ℂ (fun s => riemannZeta s ^ d) {s : ℂ | 1 < s.re} := fun s hs =>
    ((differentiableAt_riemannZeta fun h => by
      rw [h] at hs; simp at hs).pow d).differentiableWithinAt
  have hznz : ∀ s : ℂ, 1 < s.re → riemannZeta s ^ d ≠ 0 := fun s hs =>
    pow_ne_zero d (riemannZeta_ne_zero_of_one_lt_re hs)
  have hM : ∀ w, netMultiplicity z m w = 0 := by
    intro w
    by_contra hw
    obtain ⟨w₀, hw₀, htop⟩ := exists_top_netMultiplicity hw
    have hneg := rationalDeformation_anchor
      (fun n => mul_nonneg (Nat.cast_nonneg d) ArithmeticFunction.vonMangoldt_nonneg)
      (abscissaOfAbsConv_zeta_pow_le_one d) hzd hznz
      (fun s hs => neg_logDeriv_zeta_pow_eq_LSeries d hs) hS.posDef_neg_logDeriv hF hw₀ htop
    have hzero := eq_zero_of_pole_of_eq_mul_rationalMultiplier
      (hS.entire_Λ.mul (by fun_prop : Differentiable ℂ fun s : ℂ => (s * (s - 1)) ^ (d - κ))
        ).continuous (zetaPow_base_differentiable κ d).continuous
      (fun s hs => zetaPow_completion_eq hS hF hs) hneg
    have := (zetaPow_base_real_zero hzero).1
    omega
  have hR1 : ∀ s : ℂ, (∀ i, s ≠ z i) → rationalMultiplier z m s = 1 := fun s hs =>
    rationalMultiplier_eq_one_of_netMultiplicity_eq_zero hM hs
  -- `F = ζ^d` on `Re s > 1` by continuity across the finite multiplier set
  have hFeq : ∀ x : ℂ, 1 < x.re → F x = riemannZeta x ^ d := by
    intro x hx
    have hev : ∀ᶠ s in 𝓝[≠] x, F s = riemannZeta s ^ d := by
      filter_upwards [eventually_ne_multiplierPoints z x,
        nhdsWithin_le_nhds (hU.mem_nhds hx)] with s hs hs1
      rw [hF s hs1, hR1 s hs, mul_one]
    have hFc : ContinuousAt F x :=
      ((hS.diffOn_F x hx).differentiableAt (hU.mem_nhds hx)).continuousAt
    have hζc : ContinuousAt (fun s => riemannZeta s ^ d) x :=
      ((hzd x hx).differentiableAt (hU.mem_nhds hx)).continuousAt
    exact tendsto_nhds_unique (hFc.tendsto.mono_left nhdsWithin_le_nhds)
      ((hζc.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun s hs => hs.symm))
  refine ⟨?_, hFeq⟩
  -- at `s = 1` the completion identity reads `Λ(1) · 0^{d−κ} = (2ξ(1))^d ≠ 0` unless `κ = d`
  by_contra hne
  have hlt : κ < d := lt_of_le_of_ne hκ hne
  have hcont : ∀ x : ℂ, Λ x * (x * (x - 1)) ^ (d - κ) =
      (x * (x - 1)) ^ (κ - d) * (2 * RHTower.xi x) ^ d := by
    intro x
    have hev : ∀ᶠ s in 𝓝[≠] x, Λ s * (s * (s - 1)) ^ (d - κ) =
        (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d := by
      filter_upwards [eventually_ne_multiplierPoints z x] with s hs
      rw [zetaPow_completion_eq hS hF hs, hR1 s hs, mul_one]
    exact tendsto_nhds_unique
      (((hS.entire_Λ.mul (by fun_prop : Differentiable ℂ
        fun s : ℂ => (s * (s - 1)) ^ (d - κ))).continuous.tendsto x).mono_left
        nhdsWithin_le_nhds)
      ((((zetaPow_base_differentiable κ d).continuous.tendsto x).mono_left
        nhdsWithin_le_nhds).congr' (hev.mono fun s hs => hs.symm))
  have h1 := hcont 1
  have hd0 : κ - d = 0 := by omega
  have hdk : d - κ ≠ 0 := by omega
  simp only [hd0, pow_zero, sub_self, mul_zero, zero_pow hdk, one_mul] at h1
  have hxi1 : (2 * RHTower.xi (1 : ℂ)) ^ d ≠ 0 :=
    pow_ne_zero d (mul_ne_zero two_ne_zero (by
      simpa using RHTower.xi_ne_zero_of_real 1))
  exact hxi1 h1.symm

/-- **Boundary capacity of rational deformations of `ζ^d`.** If a rational deformation of `ζ^d` in
`CompletedPositiveSystem κ d` has a zero on the boundary line `Re s = 1`, then `d < κ` and, for every
finite set `Z` of positive heights, `2 Σ_{β ∈ Z} M(1 + iβ) ≤ κ − d`. The lattice pole budget `d` of
`ζ^d` is spent on the logarithmic lattice and cannot pay for boundary zeros, so the capacity `κ/2`
is never attained; the boundary twists (`κ = d + 2r` with `r` boundary zeros) are optimal. -/
theorem rationalDeformation_zetaPow_boundary_capacity {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℤ}
    (hF : ∀ s : ℂ, 1 < s.re → F s = riemannZeta s ^ d * rationalMultiplier z m s)
    {β₀ : ℝ} (hβ₀ : 0 < netMultiplicity z m (1 + (β₀ : ℂ) * I)) :
    d < κ ∧ ∀ Z : Finset ℝ, (∀ β ∈ Z, 0 < β) →
      2 * ∑ β ∈ Z, netMultiplicity z m (1 + (β : ℂ) * I) ≤ (κ : ℤ) - d := by
  have hzd : DifferentiableOn ℂ (fun s => riemannZeta s ^ d) {s : ℂ | 1 < s.re} := fun s hs =>
    ((differentiableAt_riemannZeta fun h => by
      rw [h] at hs; simp at hs).pow d).differentiableWithinAt
  have hznz : ∀ s : ℂ, 1 < s.re → riemannZeta s ^ d ≠ 0 := fun s hs =>
    pow_ne_zero d (riemannZeta_ne_zero_of_one_lt_re hs)
  have hb : ∀ n, 0 ≤ (d : ℝ) * ArithmeticFunction.vonMangoldt n := fun n =>
    mul_nonneg (Nat.cast_nonneg d) ArithmeticFunction.vonMangoldt_nonneg
  have hd1 := hS.degree_pos
  have hL := fun (s : ℂ) (hs : 1 < s.re) => neg_logDeriv_zeta_pow_eq_LSeries d hs
  have hΛm : Differentiable ℂ fun s : ℂ => Λ s * (s * (s - 1)) ^ (d - κ) :=
    hS.entire_Λ.mul (by fun_prop)
  have hpole : ∀ w : ℂ, netMultiplicity z m w < 0 →
      (w * (w - 1)) ^ (κ - d) * (2 * RHTower.xi w) ^ d = 0 := fun w hw =>
    eq_zero_of_pole_of_eq_mul_rationalMultiplier hΛm.continuous
      (zetaPow_base_differentiable κ d).continuous (fun s hs => zetaPow_completion_eq hS hF hs) hw
  -- the top of the weighted points is the real anchor `1`
  obtain ⟨w₀, hw₀, htop⟩ := exists_top_netMultiplicity hβ₀.ne'
  have hneg := rationalDeformation_anchor hb (abscissaOfAbsConv_zeta_pow_le_one d) hzd hznz hL
    hS.posDef_neg_logDeriv hF hw₀ htop
  obtain ⟨hdκ, h01⟩ := zetaPow_base_real_zero (hpole _ hneg)
  have hge : 1 ≤ w₀.re := by
    have := htop _ hβ₀.ne'; simpa using this
  have hσ1 : w₀.re = 1 := by rcases h01 with h | h <;> [linarith; exact h]
  refine ⟨hdκ, fun Z hZ => ?_⟩
  have hσ : ∀ w : ℂ, netMultiplicity z m w ≠ 0 → w.re ≤ 1 := fun w hw => hσ1 ▸ htop w hw
  have hD := rationalDeformation_lineResidue_isEvenPosDef hb (abscissaOfAbsConv_zeta_pow_le_one d)
    hzd hznz hL hS.posDef_neg_logDeriv hF (σ := 1) hσ
  -- no poles on the boundary line off `s = 1`
  have hnp : ∀ β : ℝ, β ≠ 0 → 0 ≤ netMultiplicity z m (((1 : ℝ) : ℂ) + (β : ℂ) * I) := by
    intro β hβ
    by_contra hlt
    have h0 := hpole _ (not_le.mp hlt)
    rcases mul_eq_zero.mp h0 with h1 | h2
    · have h1' := pow_eq_zero_iff (by omega : κ - d ≠ 0) |>.mp h1
      rcases mul_eq_zero.mp h1' with h | h
      · have := congrArg Complex.re h; simp at this
      · have := congrArg Complex.im h; simp at this; exact hβ this
    · have h2' := (pow_eq_zero_iff (by omega : d ≠ 0)).mp h2
      have hξ := (mul_eq_zero.mp h2').resolve_left two_ne_zero
      have := RHTower.xi_zero_re_lt_one hξ
      simp at this
  have hcap := total_zero_mass_le hD (fun β hβ => by
    have := hnp β hβ; simp only [neg_nonpos]; exact_mod_cast this) hZ
  simp only [neg_neg, Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_one] at hcap
  -- the anchor order: `−M(1) ≤ κ − d`
  have hord := analyticOrderAt_add_eq_of_eq_mul_rationalMultiplier hΛm
    (zetaPow_base_differentiable κ d) (fun s hs => zetaPow_completion_eq hS hF hs) 1
  have hneg1 : netMultiplicity z m 1 < 0 := by
    have h := hneg; rw [hσ1] at h; simpa using h
  have hk₂ : (netMultiplicity z m 1).toNat = 0 := by omega
  rw [hk₂, Nat.cast_zero, add_zero] at hord
  have hbase : analyticOrderAt (fun s : ℂ => (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d)
      1 = (κ - d : ℕ) := by
    have h1 : AnalyticAt ℂ (fun s : ℂ => s * (s - 1)) 1 := by fun_prop
    have hord1 : analyticOrderAt (fun s : ℂ => s * (s - 1)) 1 = 1 := by
      rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) by rfl, h1.analyticOrderAt_eq_natCast]
      exact ⟨fun s => s, analyticAt_id, one_ne_zero, Eventually.of_forall fun s => by
        simp [mul_comm]⟩
    have h2 : AnalyticAt ℂ (fun s : ℂ => (2 * RHTower.xi s) ^ d) 1 :=
      (completedPositiveSystem_riemannZeta.entire_Λ.analyticAt 1).pow d
    have h2ne : (2 * RHTower.xi 1) ^ d ≠ 0 :=
      pow_ne_zero d (mul_ne_zero two_ne_zero (by simpa using RHTower.xi_ne_zero_of_real 1))
    rw [show (fun s : ℂ => (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d) =
        (fun s : ℂ => s * (s - 1)) ^ (κ - d) * fun s : ℂ => (2 * RHTower.xi s) ^ d from rfl,
      analyticOrderAt_mul (h1.pow _) h2, analyticOrderAt_pow h1, hord1,
      h2.analyticOrderAt_eq_zero.mpr h2ne, add_zero]
    simp
  rw [hbase] at hord
  have hk : (-netMultiplicity z m 1).toNat ≤ κ - d := by
    have h : (((-netMultiplicity z m 1).toNat : ℕ) : ℕ∞) ≤ ((κ - d : ℕ) : ℕ∞) := by
      rw [← hord]; exact le_add_self
    exact_mod_cast h
  have hk' : -netMultiplicity z m 1 ≤ (κ : ℤ) - d := by
    have := Int.toNat_of_nonneg (show 0 ≤ -netMultiplicity z m 1 by omega)
    omega
  have hcapZ : (2 : ℝ) * ∑ β ∈ Z, ((netMultiplicity z m (1 + (β : ℂ) * I) : ℤ) : ℝ) ≤
      -((netMultiplicity z m 1 : ℤ) : ℝ) := by
    linarith
  have hcapZ' : 2 * ∑ β ∈ Z, netMultiplicity z m (1 + (β : ℂ) * I) ≤ -netMultiplicity z m 1 := by
    exact_mod_cast hcapZ
  linarith

end GaloisForLFunctions.BiarithmeticGaugeGeometry
