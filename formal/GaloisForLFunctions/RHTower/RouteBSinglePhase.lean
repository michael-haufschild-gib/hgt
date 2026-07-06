/-
The single-phase harmonic small-ball law of the (SMOOTH-LOW) architecture.

A circle sum in the harmonics of ONE phase — `θ ↦ leadC · ∏_j (e^{iθ} − z_j)`, the
value of a degree-`n` polynomial evaluated on the unit circle — is anti-concentrated
with exponent `1/n`: its sublevel set at level `r` has measure at most
`n · 2π · √(2·(r/‖leadC‖)^{1/n})`.

The mechanism factors the product: if `‖leadC · ∏_j (e^{iθ} − z_j)‖ ≤ r` then the
product of the `n` chord lengths is `≤ r/‖leadC‖`, so at least one chord length is
`≤ (r/‖leadC‖)^{1/n}`, placing `θ` in one of `n` single-root arcs, each of which is a
radial caustic band. This is the genuine anti-concentration of a single non-linear
phase: a power law in `r`, never a point mass, but degrading as `1/n` with the harmonic
depth — so a single phase alone does not reach the two-dimensional `r²` rate; that
requires spreading mass across multiplicatively independent phases.

* `root_arc_measure` — the single-root arc `{θ : ‖e^{iθ} − z‖ ≤ s}` has measure
  `≤ 2π·√(2s)`, uniformly in the center `z`.
* `exists_factor_le` — a product of `n` nonnegative reals `≤ M` has a factor
  `≤ M^{1/n}`.
* `prod_circle_sublevel` — the single-phase degree-`n` sublevel `1/n`-law.
-/
import GaloisForLFunctions.RHTower.RouteBSublevel

namespace RHTower
namespace Sublevel

open Complex MeasureTheory
open scoped ENNReal

/-- **The single-root arc measure.**  The set of angles in `[0, 2π]` at which the unit
circle passes within `s` of a center `z` has measure at most `2π·√(2s)`, uniformly in
`z`.  For `s > 1/2` the total-measure bound `2π` already suffices; for `s ≤ 1/2` a
nonempty arc forces `‖z‖ ≥ 1 − s ≥ 1/2` by the reverse triangle inequality, and the
radial caustic band bound applies. -/
theorem root_arc_measure (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖Complex.exp ((θ : ℂ) * Complex.I) - z‖ ≤ s}
      ≤ ENNReal.ofReal (2 * Real.pi * Real.sqrt (2 * s)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases le_or_gt s (1 / 2) with hsmall | hbig
  · -- s ≤ 1/2 : either the arc is empty, or ‖z‖ ≥ 1 - s ≥ 1/2 and the radial band applies.
    rcases le_or_gt (1 - s) ‖z‖ with hz | hz
    · -- ‖z‖ ≥ 1 - s ≥ 1/2 > 0 : apply the radial caustic band bound.
      have hz0 : (0 : ℝ) < ‖z‖ := by linarith
      have hzne : z ≠ 0 := by
        intro h; rw [h, norm_zero] at hz0; exact lt_irrefl _ hz0
      have hseteq : {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
            ‖Complex.exp ((θ : ℂ) * Complex.I) - z‖ ≤ s}
          = {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
              |‖(-z) + (1 : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ - s / 2| ≤ s / 2} := by
        ext θ
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨hI, hle⟩
          refine ⟨hI, ?_⟩
          have hcong : (-z) + (1 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
              = Complex.exp ((θ : ℂ) * Complex.I) - z := by ring
          rw [hcong, abs_le]
          constructor
          · have := norm_nonneg (Complex.exp ((θ : ℂ) * Complex.I) - z); linarith
          · linarith
        · rintro ⟨hI, hle⟩
          refine ⟨hI, ?_⟩
          have hcong : (-z) + (1 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
              = Complex.exp ((θ : ℂ) * Complex.I) - z := by ring
          rw [hcong] at hle
          rw [abs_le] at hle
          linarith [hle.2]
      rw [hseteq]
      have hnegz : ((-z) : ℂ) ≠ 0 := by simpa using hzne
      have hrad := radial_band_measure (B := (1 : ℂ)) (c := -z) (ρ := s / 2) (r := s / 2)
        hnegz one_ne_zero (by linarith) (by linarith)
      refine le_trans hrad ?_
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.sqrt_le_sqrt
      -- 2·((s/2)(2·(s/2)+s/2)/(‖-z‖·‖1‖)) ≤ 2 s
      rw [norm_neg, norm_one, mul_one]
      have hstep : s / 2 * (2 * (s / 2) + s / 2) / ‖z‖ ≤ s := by
        rw [div_le_iff₀ hz0]; nlinarith [hs, hsmall, hz]
      linarith [hstep]
    · -- ‖z‖ < 1 - s : the arc is empty (reverse triangle).
      have hempty : {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
            ‖Complex.exp ((θ : ℂ) * Complex.I) - z‖ ≤ s} = ∅ := by
        ext θ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        rintro _ hle
        have hnorm : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
          rw [show ((θ : ℂ) * Complex.I) = ((θ : ℝ) : ℂ) * Complex.I from rfl,
            Complex.norm_exp_ofReal_mul_I]
        have hrev : (1 : ℝ) - ‖z‖ ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - z‖ := by
          have := norm_sub_norm_le (Complex.exp ((θ : ℂ) * Complex.I)) z
          rw [hnorm] at this; linarith
        linarith
      rw [hempty, measure_empty]; positivity
  · -- s > 1/2 : bound by the total measure 2π ≤ 2π√(2s).
    calc volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖Complex.exp ((θ : ℂ) * Complex.I) - z‖ ≤ s}
        ≤ volume (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
          apply measure_mono; rintro θ ⟨hI, _⟩; exact hI
      _ = ENNReal.ofReal (2 * Real.pi) := by
          rw [Real.volume_Icc]; congr 1; ring
      _ ≤ ENNReal.ofReal (2 * Real.pi * Real.sqrt (2 * s)) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : (1 : ℝ) ≤ Real.sqrt (2 * s) := by
            rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
            apply Real.sqrt_le_sqrt; linarith
          nlinarith [h1, hπ]

/-- **The factor-selection step.**  If a product of `n ≥ 1` nonnegative reals is at most
`M`, then some factor is at most `M^{1/n}`: otherwise every factor exceeds `M^{1/n}` and
the product exceeds `(M^{1/n})^n = M`. -/
theorem exists_factor_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (x : ι → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (h : ∏ i ∈ s, x i ≤ M) :
    ∃ i ∈ s, x i ≤ M ^ ((s.card : ℝ)⁻¹) := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hcard : s.card ≠ 0 := Finset.card_ne_zero.mpr hs
  set sval : ℝ := M ^ ((s.card : ℝ)⁻¹) with hsval
  rcases hM.eq_or_lt with hM0 | hM0
  · -- M = 0 : sval = 0, so all factors are positive, product positive, contradiction.
    have hsv0 : sval = 0 := by
      rw [hsval, ← hM0, Real.zero_rpow (by positivity : ((s.card : ℝ)⁻¹) ≠ 0)]
    have hpos : 0 < ∏ i ∈ s, x i :=
      Finset.prod_pos (fun i hi => by have := hcon i hi; rw [hsv0] at this; exact this)
    rw [← hM0] at h; linarith
  · -- M > 0 : sval > 0, strict product bound gives M < ∏ ≤ M.
    have hsvpos : 0 < sval := Real.rpow_pos_of_pos hM0 _
    have hlt : sval ^ s.card < ∏ i ∈ s, x i := by
      calc sval ^ s.card = ∏ _i ∈ s, sval := by rw [Finset.prod_const]
        _ < ∏ i ∈ s, x i :=
            Finset.prod_lt_prod_of_nonempty (fun i _ => hsvpos) (fun i hi => hcon i hi) hs
    have hpow : sval ^ s.card = M := by
      rw [hsval, ← Real.rpow_natCast (M ^ ((s.card : ℝ)⁻¹)) s.card, ← Real.rpow_mul hM,
        inv_mul_cancel₀ (by exact_mod_cast hcard), Real.rpow_one]
    rw [hpow] at hlt; linarith

/-- **The single-phase degree-`n` sublevel law.**  For a nonempty index set `s`, centers
`z_i`, and a nonzero leading coefficient, the sublevel set at level `r` of the harmonic
product `θ ↦ leadC · ∏_i (e^{iθ} − z_i)` has measure at most
`n · 2π · √(2·(r/‖leadC‖)^{1/n})`, where `n = |s|`.  This is the exponent-`1/n`
anti-concentration of a single non-linear phase: a genuine power law in `r`, obtained by
covering the sublevel set with `n` single-root radial caustic bands. -/
theorem prod_circle_sublevel {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (z : ι → ℂ) (leadC : ℂ) (hlead : leadC ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖leadC * ∏ i ∈ s, (Complex.exp ((θ : ℂ) * Complex.I) - z i)‖ ≤ r}
      ≤ (s.card : ℝ≥0∞)
          * ENNReal.ofReal (2 * Real.pi
              * Real.sqrt (2 * (r / ‖leadC‖) ^ ((s.card : ℝ)⁻¹))) := by
  classical
  have hlead0 : (0 : ℝ) < ‖leadC‖ := norm_pos_iff.mpr hlead
  set M : ℝ := r / ‖leadC‖ with hMdef
  have hM : 0 ≤ M := by rw [hMdef]; positivity
  set sval : ℝ := M ^ ((s.card : ℝ)⁻¹) with hsvaldef
  -- covering by single-root arcs
  have hcover : {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖leadC * ∏ i ∈ s, (Complex.exp ((θ : ℂ) * Complex.I) - z i)‖ ≤ r}
      ⊆ ⋃ i ∈ s, {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖Complex.exp ((θ : ℂ) * Complex.I) - z i‖ ≤ sval} := by
    rintro θ ⟨hI, hle⟩
    -- ‖leadC‖ · ∏‖·‖ ≤ r ⟹ ∏‖·‖ ≤ M
    rw [norm_mul, norm_prod] at hle
    have hprod : ∏ i ∈ s, ‖Complex.exp ((θ : ℂ) * Complex.I) - z i‖ ≤ M := by
      rw [hMdef, le_div_iff₀ hlead0]; linarith [hle, mul_comm ‖leadC‖
        (∏ i ∈ s, ‖Complex.exp ((θ : ℂ) * Complex.I) - z i‖)]
    obtain ⟨i, hi, hi_le⟩ := exists_factor_le s hs
      (fun i => ‖Complex.exp ((θ : ℂ) * Complex.I) - z i‖) hM hprod
    exact Set.mem_biUnion hi ⟨hI, hi_le⟩
  calc volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖leadC * ∏ i ∈ s, (Complex.exp ((θ : ℂ) * Complex.I) - z i)‖ ≤ r}
      ≤ volume (⋃ i ∈ s, {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖Complex.exp ((θ : ℂ) * Complex.I) - z i‖ ≤ sval}) := measure_mono hcover
    _ ≤ ∑ i ∈ s, volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖Complex.exp ((θ : ℂ) * Complex.I) - z i‖ ≤ sval} :=
        measure_biUnion_finset_le s _
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal (2 * Real.pi * Real.sqrt (2 * sval)) :=
        Finset.sum_le_sum (fun i _ =>
          root_arc_measure (z i) (Real.rpow_nonneg hM _))
    _ = (s.card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi * Real.sqrt (2 * sval)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The single-phase polynomial sublevel law.**  For a complex polynomial `p` of degree
`n ≥ 1`, the sublevel set at level `r` of `θ ↦ p(e^{iθ})` — the value of `p` on the unit
circle, i.e. a genuine polynomial in the single phase `e^{iθ}` — has measure at most
`n · 2π · √(2·(r/‖leadingCoeff p‖)^{1/n})`.  This is the anti-concentration of a single
non-linear phase: `p(e^{iθ})` traces an algebraic curve in `ℂ`, and its `r`-neighbourhood
in angle has a power-law measure with exponent `1/n`, never a point mass.  Obtained by
splitting `p` into its `n` linear factors over `ℂ` and applying the degree-`n` sublevel
law. -/
theorem poly_circle_sublevel (p : Polynomial ℂ) (hp : 1 ≤ p.natDegree) {r : ℝ} (hr : 0 ≤ r) :
    volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖p.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ r}
      ≤ (p.natDegree : ℝ≥0∞)
          * ENNReal.ofReal (2 * Real.pi
              * Real.sqrt (2 * (r / ‖p.leadingCoeff‖) ^ ((p.natDegree : ℝ)⁻¹))) := by
  classical
  have hp0 : p ≠ 0 := fun h => by rw [h] at hp; simp at hp
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hmcard : p.roots.card = p.natDegree := IsAlgClosed.card_roots_eq_natDegree (p := p)
  set s : Finset (ℂ × ℕ) := p.roots.toEnumFinset with hs
  have hscard : s.card = p.natDegree := by rw [hs, Multiset.card_toEnumFinset, hmcard]
  have hsne : s.Nonempty := by
    rw [← Finset.card_pos, hscard]; omega
  have hfactor := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) hmcard
  -- eval on the circle = leadingCoeff · ∏ over the enumerated roots of (e^{iθ} − root)
  have heval : ∀ θ : ℝ, p.eval (Complex.exp ((θ : ℂ) * Complex.I))
      = p.leadingCoeff * ∏ x ∈ s, (Complex.exp ((θ : ℂ) * Complex.I) - x.1) := by
    intro θ
    set w : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hw
    have hprodeq : ∏ x ∈ s, (w - x.1) = (p.roots.map (fun a => w - a)).prod := by
      rw [hs, Finset.prod_eq_multiset_prod]
      have hmm : (p.roots.toEnumFinset.val.map (fun x : ℂ × ℕ => w - x.1))
          = (p.roots.toEnumFinset.val.map Prod.fst).map (fun a => w - a) := by
        rw [Multiset.map_map]; rfl
      rw [hmm, Multiset.map_toEnumFinset_fst]
    rw [hprodeq]
    conv_lhs => rw [← hfactor]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
      Multiset.map_map]
    congr 1
    refine congrArg _ ?_
    apply Multiset.map_congr rfl
    intro a _
    simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hseteq : {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖p.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ r}
      = {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖p.leadingCoeff * ∏ x ∈ s, (Complex.exp ((θ : ℂ) * Complex.I) - x.1)‖ ≤ r} := by
    ext θ; simp only [Set.mem_setOf_eq]; rw [heval θ]
  rw [hseteq]
  have hmain := prod_circle_sublevel s hsne (fun x => x.1) p.leadingCoeff hlead hr
  rw [hscard] at hmain
  exact hmain

/-- **Shift-uniformity of the single-phase law.**  Adding a constant `w` to the harmonic
value does not change the sublevel bound: `‖w + p(e^{iθ})‖ ≤ r` obeys the same
degree-`n` estimate as `‖p(e^{iθ})‖ ≤ r`, because `p + C w` has the same degree and leading
coefficient as `p`.  This is the property the hierarchical argument consumes — the
single-phase bound is uniform over the value `w` obtained by conditioning on every other
phase. -/
theorem poly_circle_sublevel_shift (p : Polynomial ℂ) (hp : 1 ≤ p.natDegree) (w : ℂ)
    {r : ℝ} (hr : 0 ≤ r) :
    volume {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖w + p.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ r}
      ≤ (p.natDegree : ℝ≥0∞)
          * ENNReal.ofReal (2 * Real.pi
              * Real.sqrt (2 * (r / ‖p.leadingCoeff‖) ^ ((p.natDegree : ℝ)⁻¹))) := by
  set q : Polynomial ℂ := p + Polynomial.C w with hq
  have hqdeg : q.natDegree = p.natDegree := by rw [hq, Polynomial.natDegree_add_C]
  have hqlead : q.leadingCoeff = p.leadingCoeff := by
    have hne : p.natDegree ≠ 0 := by omega
    rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, hqdeg, hq,
      Polynomial.coeff_add, Polynomial.coeff_C, if_neg hne, add_zero]
  have hqdeg1 : 1 ≤ q.natDegree := by rw [hqdeg]; exact hp
  have hqeval : ∀ z : ℂ, q.eval z = w + p.eval z := by
    intro z; rw [hq, Polynomial.eval_add, Polynomial.eval_C, add_comm]
  have hseteq : {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
        ‖w + p.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ r}
      = {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
          ‖q.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ r} := by
    ext θ; simp only [Set.mem_setOf_eq]; rw [hqeval]
  rw [hseteq]
  have hmain := poly_circle_sublevel q hqdeg1 hr
  rw [hqdeg, hqlead] at hmain
  exact hmain

/-- **The two-phase conditioning composition.**  For two independent phases carrying
single-phase harmonic polynomials `P`, `Q` (with `deg P ≥ 1`), the joint sublevel set of
`c + P(e^{iθ}) + Q(e^{iφ})` in the product `[0,2π]²` has measure at most `2π` times the
single-phase bound for `P`.  Fixing the second phase `φ`, the value `c + Q(e^{iφ})` is an
additive constant that the shift-uniform single-phase bound absorbs, so the whole packet
inherits `P`'s anti-concentration uniformly in `φ`.  This is the hierarchical conditioning
step: the joint field is at least as anti-concentrated as any single non-linear phase in
it. -/
theorem two_single_phase_sublevel (P Q : Polynomial ℂ) (hP : 1 ≤ P.natDegree) (c : ℂ)
    {r : ℝ} (hr : 0 ≤ r) :
    (volume.prod volume)
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
        {p : ℝ × ℝ | ‖c + Q.eval (Complex.exp ((p.1 : ℂ) * Complex.I))
            + P.eval (Complex.exp ((p.2 : ℂ) * Complex.I))‖ ≤ r})
      ≤ ENNReal.ofReal (2 * Real.pi)
          * ((P.natDegree : ℝ≥0∞)
              * ENNReal.ofReal (2 * Real.pi
                  * Real.sqrt (2 * (r / ‖P.leadingCoeff‖) ^ ((P.natDegree : ℝ)⁻¹)))) := by
  classical
  set Cbound : ℝ≥0∞ := (P.natDegree : ℝ≥0∞)
      * ENNReal.ofReal (2 * Real.pi
          * Real.sqrt (2 * (r / ‖P.leadingCoeff‖) ^ ((P.natDegree : ℝ)⁻¹))) with hC
  set S : Set (ℝ × ℝ) :=
    (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
      {p : ℝ × ℝ | ‖c + Q.eval (Complex.exp ((p.1 : ℂ) * Complex.I))
          + P.eval (Complex.exp ((p.2 : ℂ) * Complex.I))‖ ≤ r} with hS
  have hcont : Continuous fun p : ℝ × ℝ =>
      ‖c + Q.eval (Complex.exp ((p.1 : ℂ) * Complex.I))
        + P.eval (Complex.exp ((p.2 : ℂ) * Complex.I))‖ := by
    apply Continuous.norm
    apply Continuous.add
    · exact continuous_const.add ((Q.continuous_aeval).comp
        (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)))
    · exact (P.continuous_aeval).comp (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hSm : MeasurableSet S := by
    apply IsClosed.measurableSet
    exact (isClosed_Icc.prod isClosed_Icc).inter (isClosed_le hcont continuous_const)
  rw [Measure.prod_apply hSm]
  have hsec : ∀ x : ℝ, volume (Prod.mk x ⁻¹' S)
      ≤ (Set.Icc (0 : ℝ) (2 * Real.pi)).indicator (fun _ => Cbound) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi)
    · rw [Set.indicator_of_mem hx, hC]
      refine le_trans (measure_mono ?_)
        (poly_circle_sublevel_shift P hP
          (c + Q.eval (Complex.exp ((x : ℂ) * Complex.I))) hr)
      rintro θ ⟨⟨_, hθI⟩, hnorm⟩
      exact ⟨hθI, hnorm⟩
    · rw [Set.indicator_of_notMem hx]
      have hempty : Prod.mk x ⁻¹' S = ∅ := by
        ext θ
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨hxI, _⟩, _⟩
        exact hx hxI
      simp [hempty]
  calc ∫⁻ x, volume (Prod.mk x ⁻¹' S)
      ≤ ∫⁻ x, (Set.Icc (0 : ℝ) (2 * Real.pi)).indicator (fun _ => Cbound) x :=
        lintegral_mono hsec
    _ = ∫⁻ _ in Set.Icc (0 : ℝ) (2 * Real.pi), Cbound :=
        lintegral_indicator measurableSet_Icc _
    _ = Cbound * volume (Set.Icc (0 : ℝ) (2 * Real.pi)) := setLIntegral_const _ _
    _ = ENNReal.ofReal (2 * Real.pi) * Cbound := by
        rw [Real.volume_Icc, mul_comm]; congr 1; ring_nf

end Sublevel
end RHTower
