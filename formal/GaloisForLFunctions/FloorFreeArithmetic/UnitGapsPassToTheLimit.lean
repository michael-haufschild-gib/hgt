import GaloisForLFunctions.HTGeometry.HurwitzZeroLimit
import GaloisForLFunctions.RHTower.BurnolSoninEvaluationNonvanishing
import GaloisForLFunctions.RHTower.ReflectedBiHeatCompletedChannels
import GaloisForLFunctions.SurfaceOfSpecZ.OneSidedHasseWeilAtTheIntegerDegrees
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheReflectionSectorsOfTheHodgeDefect

/-!
# Unit gaps pass to the limit

A count bounded by one is a statement without a floor: it does not depend on where the zero is.
Such a bound survives locally uniform limits.

* `card_zeros_le_of_tendstoLocallyUniformlyOn`, `zeros_subsingleton_of_tendstoLocallyUniformlyOn`
  (Hurwitz): if analytic functions converge locally uniformly on an open set to a function with
  isolated zeros, and infinitely many of them have at most `k` zeros there, the limit has at
  most `k` zeros there.
* `card_rightZeros_le_of_bounded_index_limit`: approximants of `ζ` with a bounded number of
  zeros right of the critical line leave `ζ` at most that many: finitely many off-line zeros.
* `forall_re_le_of_unit_gap_limit`, `riemannHypothesis_of_unit_gap_limit`: for `ζ` right of a
  line `Re s = σ` the zeros pair off under conjugation, so at most one zero is none. A sequence
  of functions analytic right of the critical line, each with at most one zero there, converging
  to `ζ`, gives the Riemann hypothesis; right of `Re s = σ` it gives the zero-free half-plane.
* `towerQuotient_eq_zero_iff`, `towerQuotient_unit_gap_iff`: the secular function
  `Λ(s)/Λ(s+N)` of the scattering tower of height `N ≥ 1` has, right of the critical line,
  exactly the zeros of `ζ`. Its count of right zeros is the same at every height, so the tower
  supplies no unit gap before the limit: it has one at some height exactly under the Riemann
  hypothesis.
-/

open Complex Filter Topology Set Metric
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open Zeta23 ArithmeticCastelnuovoSeveri

/-! ### Hurwitz: bounded counts pass to the limit -/

/-- Near a zero of the limit, all but finitely many approximants have a zero. -/
theorem eventually_exists_zero_near {U : Set ℂ} (hU : IsOpen U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hf : ContinuousOn f U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hiso : ∀ z ∈ U, f z = 0 → ∀ᶠ w in 𝓝[≠] z, f w ≠ 0) {c : ℂ} (hc : c ∈ U) (hfc : f c = 0)
    {ρ : ℝ} (hρ : 0 < ρ) : ∀ᶠ n in atTop, ∃ y, dist y c < ρ ∧ y ∈ U ∧ F n y = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc
  have hc' := hiso c hc hfc
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hc'
  obtain ⟨η, hη, hN⟩ := hc'
  set r : ℝ := min (min ε η) ρ / 2 with hr
  have hm : 0 < min (min ε η) ρ := lt_min (lt_min hε hη) hρ
  have hr0 : 0 < r := half_pos hm
  have hrε : r < ε := lt_of_lt_of_le (half_lt_self hm) ((min_le_left _ _).trans (min_le_left _ _))
  have hrη : r < η := lt_of_lt_of_le (half_lt_self hm) ((min_le_left _ _).trans (min_le_right _ _))
  have hrρ : r < ρ := lt_of_lt_of_le (half_lt_self hm) (min_le_right _ _)
  have hcl : closedBall c r ⊆ U := (closedBall_subset_ball hrε).trans hball
  have hsph : ∀ y ∈ sphere c r, f y ≠ 0 := by
    intro y hy
    have hdist : dist y c = r := mem_sphere.mp hy
    refine hN (by rw [hdist]; exact hrη) ?_
    intro hyc
    rw [mem_singleton_iff.mp hyc, dist_self] at hdist
    exact hr0.ne hdist
  have hzero := HTGeometry.eventually_exists_zero_of_tendstoUniformlyOn hr0
    (fun n => (hF n).diffContOnCl_ball hcl) (hf.mono (sphere_subset_closedBall.trans hcl))
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv _ hcl
      (isCompact_closedBall c r)) hfc hsph
  filter_upwards [hzero] with n hn
  obtain ⟨y, hy, hFy⟩ := hn
  exact ⟨y, (mem_ball.mp hy).trans hrρ, hcl (ball_subset_closedBall hy), hFy⟩

/-- **A bounded count passes to the limit.** Let `F n → f` locally uniformly on the open set
`U`, with `F n` analytic and `f` continuous with isolated zeros on `U`. If infinitely many `F n`
have at most `k` zeros in `U`, then `f` has at most `k` zeros in `U`. -/
theorem card_zeros_le_of_tendstoLocallyUniformlyOn {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hf : ContinuousOn f U) (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hiso : ∀ z ∈ U, f z = 0 → ∀ᶠ w in 𝓝[≠] z, f w ≠ 0) {k : ℕ}
    (hk : ∃ᶠ n in atTop, ∀ T : Finset ℂ, (∀ z ∈ T, z ∈ U ∧ F n z = 0) → T.card ≤ k)
    (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ U ∧ f z = 0) : S.card ≤ k := by
  classical
  -- the zeros in `S` are separated by a positive distance
  obtain ⟨d, hd, hsep⟩ : ∃ d : ℝ, 0 < d ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → d ≤ dist a b := by
    by_cases hne : S.offDiag.Nonempty
    · obtain ⟨p, hp, hmin⟩ := S.offDiag.exists_min_image (fun p => dist p.1 p.2) hne
      exact ⟨dist p.1 p.2, dist_pos.mpr (Finset.mem_offDiag.mp hp).2.2, fun a ha b hb hab =>
        hmin (a, b) (Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩)⟩
    · exact ⟨1, one_pos, fun a ha b hb hab =>
        absurd ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩⟩ hne⟩
  -- all large approximants have a zero within `d/2` of each of them
  have hall : ∀ᶠ n in atTop, ∀ c ∈ S, ∃ y, dist y c < d / 2 ∧ y ∈ U ∧ F n y = 0 :=
    (Filter.eventually_all_finset S).mpr fun c hc =>
      eventually_exists_zero_near hU hF hf hconv hiso (hS c hc).1 (hS c hc).2 (half_pos hd)
  obtain ⟨n, hn, hzeros⟩ := (hk.and_eventually hall).exists
  choose! y hy using hzeros
  have hinj : Set.InjOn y S := by
    intro a ha b hb hab
    by_contra hne
    have h1 := (hy a ha).1
    have h2 : dist (y a) b < d / 2 := by
      rw [hab]
      exact (hy b hb).1
    have h3 := hsep a ha b hb hne
    have htri : dist a b ≤ dist a (y a) + dist (y a) b := dist_triangle _ _ _
    rw [dist_comm a (y a)] at htri
    linarith only [h1, h2, h3, htri]
  have hcard := hn (S.image y) fun z hz => by
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨(hy c hc).2.1, (hy c hc).2.2⟩
  rwa [Finset.card_image_of_injOn hinj] at hcard

/-- **A unit gap passes to the limit.** If infinitely many `F n` have at most one zero in `U`,
then `f` has at most one zero in `U`. -/
theorem zeros_subsingleton_of_tendstoLocallyUniformlyOn {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hf : ContinuousOn f U) (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hiso : ∀ z ∈ U, f z = 0 → ∀ᶠ w in 𝓝[≠] z, f w ≠ 0)
    (hone : ∃ᶠ n in atTop, ∀ z ∈ U, ∀ w ∈ U, F n z = 0 → F n w = 0 → z = w)
    {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) (hfz : f z = 0) (hfw : f w = 0) : z = w := by
  classical
  by_contra hne
  have hk : ∃ᶠ n in atTop, ∀ T : Finset ℂ, (∀ z ∈ T, z ∈ U ∧ F n z = 0) → T.card ≤ 1 :=
    hone.mono fun n hn T hT => Finset.card_le_one.mpr fun a ha b hb =>
      hn a (hT a ha).1 b (hT b hb).1 (hT a ha).2 (hT b hb).2
  have hcard := card_zeros_le_of_tendstoLocallyUniformlyOn hU hF hf hconv hiso hk {z, w}
    (fun a ha => by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact ⟨hz, hfz⟩
      · rw [Finset.mem_singleton.mp ha]
        exact ⟨hw, hfw⟩)
  rw [Finset.card_pair hne] at hcard
  omega

/-! ### The zeros of `ζ` right of a line -/

/-- The half-plane right of `Re s = σ` without the pole of `ζ`. -/
def rightOfLine (σ : ℝ) : Set ℂ := {s | σ < s.re ∧ s ≠ 1}

theorem isOpen_rightOfLine (σ : ℝ) : IsOpen (rightOfLine σ) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton

theorem continuousOn_riemannZeta_rightOfLine (σ : ℝ) :
    ContinuousOn riemannZeta (rightOfLine σ) := fun _ hs =>
  (differentiableAt_riemannZeta hs.2).continuousAt.continuousWithinAt

/-- The zeros of `ζ` right of the critical line are isolated. -/
theorem eventually_riemannZeta_ne_zero_of_rightOfLine {σ : ℝ} (hσ : 0 ≤ σ) {z : ℂ}
    (hz : z ∈ rightOfLine σ) (hzero : riemannZeta z = 0) :
    ∀ᶠ w in 𝓝[≠] z, riemannZeta w ≠ 0 := by
  have h1 : z.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hzero
  exact _root_.RHTower.eventually_riemannZeta_ne_zero_nhdsNE (lt_of_le_of_lt hσ hz.1) h1

/-- **A unit gap right of a line empties it.** If functions analytic right of `Re s = σ`,
`σ ≥ 0`, infinitely many of them with at most one zero there, converge locally uniformly to
`ζ`, then no nontrivial zero of `ζ` lies right of that line. -/
theorem forall_re_le_of_unit_gap_limit {σ : ℝ} (hσ : 0 ≤ σ) {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) (rightOfLine σ))
    (hconv : TendstoLocallyUniformlyOn F riemannZeta atTop (rightOfLine σ))
    (hone : ∃ᶠ n in atTop, ∀ z ∈ rightOfLine σ, ∀ w ∈ rightOfLine σ,
      F n z = 0 → F n w = 0 → z = w) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ σ := by
  intro ρ hρ
  by_contra hgt
  have hre : σ < ρ.re := lt_of_not_ge hgt
  have hρc := _root_.RHTower.conj_mem_zetaZeroConfig hρ
  have hmem : ∀ τ ∈ zetaZeroConfig.carrier, σ < τ.re → τ ∈ rightOfLine σ := by
    intro τ hτ hτre
    refine ⟨hτre, fun h1 => ?_⟩
    have := hτ.2.2
    rw [h1, Complex.one_re] at this
    exact lt_irrefl _ this
  have heq : ρ = conj ρ :=
    zeros_subsingleton_of_tendstoLocallyUniformlyOn (isOpen_rightOfLine σ) hF
      (continuousOn_riemannZeta_rightOfLine σ) hconv
      (fun z hz hzero => eventually_riemannZeta_ne_zero_of_rightOfLine hσ hz hzero) hone
      (hmem ρ hρ hre) (hmem (conj ρ) hρc (by simpa using hre)) hρ.1 hρc.1
  apply zetaZeroConfig_im_ne_zero' ρ hρ
  have him := congrArg Complex.im heq
  simp only [Complex.conj_im] at him
  linarith only [him]

/-- **The Riemann hypothesis from a unit gap in the limit.** A sequence of functions analytic
right of the critical line, infinitely many of them with at most one zero there, converging
locally uniformly to `ζ`, gives the Riemann hypothesis. -/
theorem riemannHypothesis_of_unit_gap_limit {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) (rightOfLine (1 / 2)))
    (hconv : TendstoLocallyUniformlyOn F riemannZeta atTop (rightOfLine (1 / 2)))
    (hone : ∃ᶠ n in atTop, ∀ z ∈ rightOfLine (1 / 2), ∀ w ∈ rightOfLine (1 / 2),
      F n z = 0 → F n w = 0 → z = w) :
    RiemannHypothesis :=
  SurfaceOfSpecZ.riemannHypothesis_of_forall_re_le
    (forall_re_le_of_unit_gap_limit (by norm_num) hF hconv hone)

/-- **A bounded index gives finitely many zeros right of the line.** If functions analytic
right of the critical line, infinitely many of them with at most `k` zeros there, converge
locally uniformly to `ζ`, then `ζ` has at most `k` zeros right of the critical line. -/
theorem card_rightZeros_le_of_bounded_index_limit {F : ℕ → ℂ → ℂ} {k : ℕ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) (rightOfLine (1 / 2)))
    (hconv : TendstoLocallyUniformlyOn F riemannZeta atTop (rightOfLine (1 / 2)))
    (hk : ∃ᶠ n in atTop, ∀ T : Finset ℂ,
      (∀ z ∈ T, z ∈ rightOfLine (1 / 2) ∧ F n z = 0) → T.card ≤ k)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re) : S.card ≤ k :=
  card_zeros_le_of_tendstoLocallyUniformlyOn (isOpen_rightOfLine _) hF
    (continuousOn_riemannZeta_rightOfLine _) hconv
    (fun z hz hzero => eventually_riemannZeta_ne_zero_of_rightOfLine (by norm_num) hz hzero) hk S
    (fun ρ hρ => ⟨⟨(hS ρ hρ).2, fun h1 => by
      have := (hS ρ hρ).1.2.2
      rw [h1, Complex.one_re] at this
      exact lt_irrefl _ this⟩, (hS ρ hρ).1.1⟩)

/-! ### The scattering tower keeps the count -/

/-- The secular function of the scattering tower of height `N`: `Λ(s)/Λ(s+N)`, with
`Λ(s) = π^{−s/2} Γ(s/2) ζ(s)`. -/
def towerQuotient (N : ℕ) (s : ℂ) : ℂ :=
  _root_.RHTower.reflectedCompletedLambda s / _root_.RHTower.reflectedCompletedLambda (s + N)

/-- Right of the critical line the tower of height `N ≥ 1` vanishes exactly at the zeros of
`ζ`: the shifted factor has neither zeros nor poles there. -/
theorem towerQuotient_eq_zero_iff {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 1 / 2 < s.re) :
    towerQuotient N s = 0 ↔ riemannZeta s = 0 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hre : 1 < (s + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith only [hs, hN1]
  have hden : _root_.RHTower.reflectedCompletedLambda (s + N) ≠ 0 := by
    unfold _root_.RHTower.reflectedCompletedLambda
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hre))
      (riemannZeta_ne_zero_of_one_lt_re hre)
  have hgam : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith only [hs])
  rw [towerQuotient, div_eq_zero_iff, or_iff_left hden, _root_.RHTower.reflectedCompletedLambda,
    mul_eq_zero, or_iff_right hgam]

/-- **The tower has a unit gap at some height exactly under the Riemann hypothesis.** For
`N ≥ 1`: the secular function `Λ(s)/Λ(s+N)` has at most one zero right of the critical line
if and only if the Riemann hypothesis holds. -/
theorem towerQuotient_unit_gap_iff {N : ℕ} (hN : 1 ≤ N) :
    (∀ z ∈ rightOfLine (1 / 2), ∀ w ∈ rightOfLine (1 / 2),
      towerQuotient N z = 0 → towerQuotient N w = 0 → z = w) ↔ RiemannHypothesis := by
  constructor
  · intro hgap
    apply SurfaceOfSpecZ.riemannHypothesis_of_forall_re_le
    intro ρ hρ
    by_contra hgt
    have hre : 1 / 2 < ρ.re := lt_of_not_ge hgt
    have hρc := _root_.RHTower.conj_mem_zetaZeroConfig hρ
    have hrec : 1 / 2 < (conj ρ).re := by simpa using hre
    have hne1 : ∀ τ ∈ zetaZeroConfig.carrier, τ ≠ 1 := by
      intro τ hτ h1
      have := hτ.2.2
      rw [h1, Complex.one_re] at this
      exact lt_irrefl _ this
    have heq : ρ = conj ρ := hgap ρ ⟨hre, hne1 ρ hρ⟩ (conj ρ) ⟨hrec, hne1 _ hρc⟩
      ((towerQuotient_eq_zero_iff hN hre).mpr hρ.1)
      ((towerQuotient_eq_zero_iff hN hrec).mpr hρc.1)
    apply zetaZeroConfig_im_ne_zero' ρ hρ
    have him := congrArg Complex.im heq
    simp only [Complex.conj_im] at him
    linarith only [him]
  · intro hRH z hz w _ hzero _
    exfalso
    have hζ := (towerQuotient_eq_zero_iff hN hz.1).mp hzero
    have hhalf := hRH z hζ (fun ⟨n, hn⟩ => by
      have hzre := hz.1
      have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hcast : (-2 * ((n : ℂ) + 1)) = ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hn, hcast, Complex.ofReal_re] at hzre
      linarith only [hzre, hnn]) hz.2
    linarith only [hhalf, hz.1]

end GaloisForLFunctions.FloorFreeArithmetic
