import GaloisForLFunctions.ZeroConfigurationGeometry.TiltedInghamInequality
import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt
import GaloisForLFunctions.SquareRootThreshold.NyquistResolutionOfTheWeilForm
import GaloisForLFunctions.SquareRootThreshold.FiniteOffLineSetsAreVisible
import GaloisForLFunctions.SquareRootThreshold.EvenAndOddTwoBumpTestsDecideTheCriticalLine
import GaloisForLFunctions.RHTower.DeBruijnHeatFlowRealZeros
import GaloisForLFunctions.RHTower.GaussianDirichletSeries

/-!
# Shallow pairs are near-collisions

`HidingNeedsNearCollisions` locates cancelling clusters of on-line configurations: they need two
heights closer than the resolution scale. This module removes the on-line hypothesis. The two
points `½ ± δ + iγ` of an FE pair share their height, so they are a collision in height that
only the depth separates. The camera resolves the pair at the cost of the pair gap
`A(2δ) − A(0) ≍ δ²` (`pairGap_pos`), and the block Ingham inequality turns this into an
identification theorem.

* **Tilted resolution** (`eq_of_weil_eq_of_pairSeparated`). Two tempered configurations with
  depths `≤ s`, whose union has `g`-separated heights apart from FE partners, are equal as soon as
  their Weil forms agree on every `C²` test supported in `[−a, a]`, `a > V/2`, and the block
  constant `D₀ − 2R(g, s, V)` is positive. Here `D₀` bounds `A(0) = 2/a_V` and every pair gap from
  below.
* **Explicit scales** (`pairGap_ge`, `tiltB_le`). For `|δ| ≤ s` the pair gap is at least
  `(π² − 8)δ²/(a a'²)`, and the neighbour tail is `B' ≤ (4π²/9)(a'/g)²`.
* **The tilted near-collision constraint** (`exists_near_pair_or_shallow_pair_of_mimic`). If two
  configurations with different carriers are mimics at aperture `a > V/2`, and
  `(16π²/9) a² a'² cosh(2sV) < (π² − 8) ε² g²`, `0 < ε ≤ s`, `g > 2a'`, then the union contains
  two points of different FE orbits at height distance `< g`, or a point deeper than `s`, or an
  off-line point shallower than `ε`.

* **Aligned pairs and the dark sector** (`pairWeight_modScaledBump_eq_sq`, `InDarkSector`). For the
  real even bump modulated to `γ₀`, the pair weight at `γ − iδ` is `Q = κ̂(γ − γ₀ − iδ)²`, and the
  two coefficients of a pair are `cQ`, `cQ̄`. Their cross term is `c² Re Q² = c² Re κ̂⁴`. The block
  degenerates only in the antialigned direction, so a pair with `Re κ̂⁴ ≥ 0` is resolved with the
  gap `A(0)` of a real point, whatever its depth. Only pairs in the dark sector `Re κ̂⁴ < 0` need
  the pair gap.
* **The dark sector lies where the camera is dim** (`norm_paperFT_tilt_sub_le`,
  `not_inDarkSector_of_bright`, `exists_near_pair_or_dim_shallow_pair_of_mimic`). The tilt moves
  `κ̂_w(x)` by at most `(e^{|δ|w} − 1)‖κ_w‖₁`, and fourth powers of points within `|x|/8` of a real
  `x` stay in the right half-plane. So a hiding shallow pair of depth `< ε` sits at a height where
  `|κ̂_w(γ − γ₀)| < 8(e^{εw} − 1)‖κ_w‖₁`: near a real zero of the camera transform or in its tail.

Proof of resolution. The two-bump tests at height `γ₀` and lags `|v| ≤ V` lie in the aperture, so
the signed lag structure vanishes on `[−V, V]`. Grouped by height it is
`Σ_k e^{iγ_k v}(c_k Q_k e^{δ_k v} + c_k Q̄_k e^{−δ_k v})`, `Q_k` the pair weight
(`coefTerm_eq_weight`, `coefTerm_reflect_eq_weight`). The pair resolution
`eq_zero_of_pairSum_eq_zero` makes every coefficient vanish, and the pair weight of the bump
modulated to `γ₀` is nonzero at height `γ₀` (`pairWeight_modScaledBump_ne_zero`).

The scale condition reads `g ≳ a a' √cosh(2sV) / ε`: a pair of depth `ε` in the dark sector is
resolved only against sites at distance of order `1/ε`. Shallow pairs are near-collisions of the
pair with itself, and they are dangerous only where the camera is dim.
-/

open Complex MeasureTheory Set
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold _root_.RHTower

theorem reflect_re' (z : ℂ) : (reflect z).re = 1 - z.re := by simp [reflect]

theorem reflect_im' (z : ℂ) : (reflect z).im = z.im := by simp [reflect]

/-- The pair weight of the real even bump modulated to `γ₀` is a square:
`Q = κ̂_w(γ − γ₀ − iδ)²`. -/
theorem pairWeight_modScaledBump_eq_sq (w γ₀ δ γ : ℝ) :
    pairWeight (modScaledBump w γ₀) δ γ =
      paperFT (scaledBump w) (((γ - γ₀ : ℝ) : ℂ) - I * δ) ^ 2 := by
  have hmod : ∀ z : ℂ, paperFT (modScaledBump w γ₀) z = paperFT (scaledBump w) (z - γ₀) :=
    fun z => paperFT_modulate (scaledBump w) γ₀ z
  have e1 : (γ : ℂ) - I * δ - γ₀ = ((γ - γ₀ : ℝ) : ℂ) - I * δ := by push_cast; ring
  have e2 : conj ((γ : ℂ) + I * δ - γ₀) = ((γ - γ₀ : ℝ) : ℂ) - I * δ := by
    apply Complex.ext <;> simp
  rw [pairWeight, hmod, hmod, conj_paperFT_scaledBump, e1, e2, sq]

/-- **The dark sector.** The camera `κ_w` modulated to the height of `ρ₀` meets the FE pair of `ρ`
in its dark sector when `Re κ̂_w(γ − γ₀ − iδ)⁴ < 0`. Outside it the two pair coefficients are
aligned and the pair is resolved like a real point. -/
def InDarkSector (w : ℝ) (ρ ρ₀ : ℂ) : Prop :=
  (paperFT (scaledBump w) (((ρ.im - ρ₀.im : ℝ) : ℂ) - I * ((ρ.re - 1 / 2 : ℝ) : ℂ)) ^ 4).re < 0

/-- The sites of two configurations: the points of their union on or right of the line. -/
def pairSites (Z Z' : ZeroConfig) : Set ℂ := {z | z ∈ Z.carrier ∪ Z'.carrier ∧ 1 / 2 ≤ z.re}

/-- The coefficient of `e^{δv}` at a site, seen by the bump `κ_w` modulated to `γ₀`. -/
def siteP (Z Z' : ZeroConfig) (w γ₀ : ℝ) (k : ℂ) : ℂ :=
  multDiff Z Z' k * pairWeight (modScaledBump w γ₀) (k.re - 1 / 2) k.im

/-- The coefficient of `e^{−δv}` at a site (zero on the line). -/
def siteQ (Z Z' : ZeroConfig) (w γ₀ : ℝ) (k : ℂ) : ℂ :=
  if k.re = 1 / 2 then 0 else
    multDiff Z Z' (reflect k) * conj (pairWeight (modScaledBump w γ₀) (k.re - 1 / 2) k.im)

/-- **The signed lag structure as a pair sum.** If the Weil forms agree on `C²` tests supported in
`[−a, a]`, then for the bump `κ_w` modulated to any height and `V/2 + w ≤ a`, the pair sum over the
sites vanishes on `[−V, V]`. -/
theorem pairSum_vanishes_of_weil_eq (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {V w a : ℝ} (hw0 : 0 < w) (hVa : V / 2 + w ≤ a) (γ₀ : ℝ)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) :
    ∀ v ∈ Icc (-V) V, ∑' k : pairSites Z Z', cexp (I * (k : ℂ).im * v) *
      (siteP Z Z' w γ₀ k * cexp ((((k : ℂ).re - 1 / 2 : ℝ) : ℂ) * v) +
        siteQ Z Z' w γ₀ k * cexp (-(((k : ℂ).re - 1 / 2 : ℝ) : ℂ) * v)) = 0 := by
  classical
  set c := multDiff Z Z' with hcdef
  set b := modScaledBump w γ₀ with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w γ₀
  have hbs := modScaledBump_support hw0 γ₀
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  -- the signed lag structure vanishes on `[−V, V]`
  have hvan : ∀ v ∈ Icc (-V) V, ∑' z, coefTerm c b v z = 0 := by
    intro v hv
    have hva : (((2 : ℕ) : ℝ) - 1) / 2 * |v| + w ≤ a := by
      have := abs_le.mpr hv
      rw [show (((2 : ℕ) : ℝ) - 1) / 2 = 1 / 2 by norm_num]
      linarith
    have hpol := lagStructure_eq_of_weil_twoBump_eq_at Z Z' hZ hZ' hb hbs |v| fun τ _ =>
      hW _ (contDiff_bumpTest hb |v| ![1, τ])
        (tsupport_bumpTest_subset hbs (abs_nonneg v) hva ![1, τ])
    have hS : lagStructure Z b v = lagStructure Z' b v := by
      rcases le_or_gt 0 v with h | h
      · rw [abs_of_nonneg h] at hpol
        exact hpol.1
      · rw [abs_of_neg h, neg_neg] at hpol
        exact hpol.2
    rw [← (lagStructure_sub_eq Z Z' hZ hZ' hb hbs v).2, hS, sub_self]
  set U := Z.carrier ∪ Z'.carrier with hU
  set K : Set ℂ := pairSites Z Z' with hK
  have hc0 : ∀ z, z ∉ U → c z = 0 := fun z hz => by
    by_contra h
    exact hz (mem_carrier_of_multDiff_ne_zero h)
  have hreflU : ∀ z, reflect z ∈ U ↔ z ∈ U := fun z => by
    rw [hU, Set.mem_union, Set.mem_union, reflect_mem_iff, reflect_mem_iff]
  -- the pair term of a site is its share of the signed lag structure
  set G : ℝ → ℂ → ℂ := fun v z => {z : ℂ | z.re = 1 / 2}.indicator (coefTerm c b v) z +
    {z : ℂ | 1 / 2 < z.re}.indicator (fun z => coefTerm c b v z + coefTerm c b v (reflect z)) z
    with hG
  have hsite : ∀ (v : ℝ) (k : K), cexp (I * (k : ℂ).im * v) *
      (siteP Z Z' w γ₀ k * cexp ((((k : ℂ).re - 1 / 2 : ℝ) : ℂ) * v) +
        siteQ Z Z' w γ₀ k * cexp (-(((k : ℂ).re - 1 / 2 : ℝ) : ℂ) * v)) = G v k := by
    intro v k
    have e1 := coefTerm_eq_weight hb.continuous hbc c (k : ℂ) v
    have e2 := coefTerm_reflect_eq_weight hb.continuous hbc c (k : ℂ) v
    have ex : ∀ x : ℝ, ((Real.exp x : ℝ) : ℂ) = cexp (x : ℂ) := fun x => Complex.ofReal_exp x
    rw [ex] at e1 e2
    simp only [siteP, siteQ, ← hcdef, ← hbdef]
    by_cases hk : (k : ℂ).re = 1 / 2
    · rw [hG]
      simp only
      rw [Set.indicator_of_mem (show (k : ℂ) ∈ {z : ℂ | z.re = 1 / 2} from hk),
        Set.indicator_of_notMem (show (k : ℂ) ∉ {z : ℂ | 1 / 2 < z.re} from fun h => by
          simp only [Set.mem_setOf_eq] at h; linarith), add_zero, e1]
      simp only [hk, if_true]
      push_cast
      ring_nf
    · have hk' : 1 / 2 < (k : ℂ).re := lt_of_le_of_ne k.2.2 (Ne.symm hk)
      rw [hG]
      simp only
      rw [Set.indicator_of_notMem (show (k : ℂ) ∉ {z : ℂ | z.re = 1 / 2} from hk),
        Set.indicator_of_mem (show (k : ℂ) ∈ {z : ℂ | 1 / 2 < z.re} from hk'), zero_add, e1, e2]
      simp only [hk, if_false]
      push_cast
      ring_nf
  -- `G v` vanishes off the sites
  have hGoff : ∀ v z, z ∉ K → G v z = 0 := by
    intro v z hz
    rw [hG]
    simp only
    by_cases hre : 1 / 2 ≤ z.re
    · have hzU : z ∉ U := fun h => hz ⟨h, hre⟩
      have h1 : coefTerm c b v z = 0 := by rw [coefTerm, hc0 z hzU, zero_mul, zero_mul]
      have h2 : coefTerm c b v (reflect z) = 0 := by
        rw [coefTerm, hc0 _ (mt (hreflU z).mp hzU), zero_mul, zero_mul]
      by_cases he : z.re = 1 / 2
      · rw [Set.indicator_of_mem (show z ∈ {z : ℂ | z.re = 1 / 2} from he), h1,
          Set.indicator_of_notMem (show z ∉ {z : ℂ | 1 / 2 < z.re} from fun h => by
            simp only [Set.mem_setOf_eq] at h; linarith), add_zero]
      · rw [Set.indicator_of_notMem (show z ∉ {z : ℂ | z.re = 1 / 2} from he),
          Set.indicator_of_mem (show z ∈ {z : ℂ | 1 / 2 < z.re} from
            lt_of_le_of_ne hre (Ne.symm he)), h1, h2]
        ring
    · push Not at hre
      rw [Set.indicator_of_notMem (show z ∉ {z : ℂ | z.re = 1 / 2} from fun h => by
          simp only [Set.mem_setOf_eq] at h; linarith),
        Set.indicator_of_notMem (show z ∉ {z : ℂ | 1 / 2 < z.re} from fun h => by
          simp only [Set.mem_setOf_eq] at h; linarith), add_zero]
  intro v hv
  have hf := (lagStructure_sub_eq Z Z' hZ hZ' hb hbs v).1
  obtain ⟨hR, hsplit⟩ := tsum_split_reflect hf
  rw [tsum_congr (hsite v), tsum_subtype K (G v)]
  have hind : K.indicator (G v) = G v := by
    funext z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hGoff v z hz]
  rw [hind, hG]
  simp only
  rw [Summable.tsum_add (hf.indicator _) hR, ← hsplit, hvan v hv]

/-- The site coefficients are summable. -/
theorem summable_site (Z Z' : ZeroConfig) (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    {w : ℝ} (hw0 : 0 < w) (γ₀ : ℝ) :
    Summable fun k : pairSites Z Z' => ‖siteP Z Z' w γ₀ k‖ + ‖siteQ Z Z' w γ₀ k‖ := by
  set c := multDiff Z Z' with hcdef
  set b := modScaledBump w γ₀ with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w γ₀
  have hbs := modScaledBump_support hw0 γ₀
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  have hf0 := (lagStructure_sub_eq Z Z' hZ hZ' hb hbs 0).1
  have hpn : ∀ k : pairSites Z Z', ‖siteP Z Z' w γ₀ k‖ = ‖coefTerm c b 0 k‖ := fun k => by
    rw [coefTerm_eq_weight hb.continuous hbc c (k : ℂ) 0]
    simp [siteP, ← hcdef, ← hbdef]
  have hqn : ∀ k : pairSites Z Z', ‖siteQ Z Z' w γ₀ k‖ ≤ ‖coefTerm c b 0 (reflect k)‖ := fun k => by
    rw [coefTerm_reflect_eq_weight hb.continuous hbc c (k : ℂ) 0]
    simp only [siteQ, ← hcdef, ← hbdef]
    split_ifs
    · rw [norm_zero]; exact norm_nonneg _
    · simp
  have hrinj : Function.Injective fun k : pairSites Z Z' => reflect (k : ℂ) := fun x y h =>
    Subtype.ext (by
      have := congrArg reflect h
      simpa [Zeta23.reflect_reflect] using this)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((hf0.norm.comp_injective Subtype.val_injective).add (hf0.norm.comp_injective hrinj))
  rw [hpn k]
  exact add_le_add le_rfl (hqn k)

/-- Distinct sites have heights at least `g` apart when the union is separated apart from FE
partners. -/
theorem sites_sep {Z Z' : ZeroConfig} {g : ℝ}
    (hsep : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ →
      ρ' ≠ reflect ρ → g ≤ |ρ.im - ρ'.im|) :
    ∀ j l : pairSites Z Z', j ≠ l → g ≤ |(j : ℂ).im - (l : ℂ).im| := by
  intro j l hjl
  refine hsep j j.2.1 l l.2.1 (fun h => hjl (Subtype.ext h.symm)) fun h => hjl ?_
  apply Subtype.ext
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rw [reflect_re'] at hre
  rw [reflect_im'] at him
  have h1 := j.2.2
  have h2 := l.2.2
  apply Complex.ext <;> linarith

/-- A nonzero signed multiplicity has a representative on or right of the line. -/
theorem exists_site_of_multDiff_ne_zero {Z Z' : ZeroConfig} {ρ₀ : ℂ} (hc : multDiff Z Z' ρ₀ ≠ 0) :
    ∃ t₀ : ℂ, 1 / 2 ≤ t₀.re ∧ multDiff Z Z' t₀ ≠ 0 := by
  by_cases h : 1 / 2 ≤ ρ₀.re
  · exact ⟨ρ₀, h, hc⟩
  · refine ⟨reflect ρ₀, by rw [reflect_re']; linarith, ?_⟩
    rwa [multDiff_reflect]

/-- **Tilted resolution of the Weil form.** Tempered configurations with depths `≤ s` whose union
has `g`-separated heights apart from FE partners, with pair gaps `≥ D₀`, `D₀ ≤ A(0)`, and positive
block constant, are determined by their Weil forms on `C²` tests supported in `[−a, a]`,
`a > V/2`. -/
theorem eq_of_weil_eq_of_pairSeparated (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {g V s D₀ a : ℝ} (hg : 0 < g) (hV : 0 < V) (hs : 0 ≤ s)
    (hdepth : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, |ρ.re - 1 / 2| ≤ s)
    (hsep : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, ∀ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ →
      ρ' ≠ reflect ρ → g ≤ |ρ.im - ρ'.im|)
    (hgap : 2 * tiltA V s < g) (hD0 : D₀ ≤ 2 / inghamA V)
    (hDpair : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, ρ.re ≠ 1 / 2 → D₀ ≤ pairGap V (ρ.re - 1 / 2) ∨
      ∀ ρ₀ ∈ Z.carrier ∪ Z'.carrier, ¬ InDarkSector (a - V / 2) ρ ρ₀)
    (hpos : 0 < D₀ - 2 * (2 * inghamA V * Real.cosh (2 * s * V) / tiltA V s ^ 2 * tiltB V g s))
    (ha : V / 2 < a)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  classical
  set w := a - V / 2 with hw
  have hw0 : 0 < w := by rw [hw]; linarith
  refine eq_of_multDiff_eq_zero fun ρ₀ => ?_
  by_contra hc
  obtain ⟨t₀, ht₀re, hct₀⟩ := exists_site_of_multDiff_ne_zero hc
  set γ₀ := t₀.im
  have hzero := pairSum_vanishes_of_weil_eq Z Z' hZ hZ' hw0 (by rw [hw]; linarith) γ₀ hW
  have hsum := summable_site Z Z' hZ hZ' hw0 γ₀
  have hres := eq_zero_of_pairSum_eq_zero (fun k : pairSites Z Z' => (k : ℂ).im)
    (fun k => (k : ℂ).re - 1 / 2) (fun k => siteP Z Z' w γ₀ k) (fun k => siteQ Z Z' w γ₀ k)
    hg hV hs (fun k => hdepth k k.2.1) (sites_sep hsep) hgap
    (fun k => by
      by_cases hk : (k : ℂ).re = 1 / 2
      · right
        exact ⟨hD0, by simp [siteQ, hk]⟩
      · rcases hDpair k k.2.1 hk with h | hbright
        · exact Or.inl h
        · -- outside the dark sector the coefficients `c Q`, `c Q̄` are aligned
          refine Or.inr ⟨hD0, ?_⟩
          have hdark := hbright t₀ (mem_carrier_of_multDiff_ne_zero hct₀)
          rw [InDarkSector, not_lt] at hdark
          have hcr : conj (multDiff Z Z' k) = multDiff Z Z' k := conj_multDiff Z Z' k
          have hcref : multDiff Z Z' (reflect k) = multDiff Z Z' k := multDiff_reflect Z Z' k
          have hQ := pairWeight_modScaledBump_eq_sq w γ₀ ((k : ℂ).re - 1 / 2) (k : ℂ).im
          have hcreal : multDiff Z Z' k = ((multDiff Z Z' k).re : ℂ) := by
            conv_lhs => rw [← Complex.re_add_im (multDiff Z Z' k)]
            have him : (multDiff Z Z' k).im = 0 := by
              have := congrArg Complex.im hcr
              rw [Complex.conj_im] at this
              linarith
            rw [him]; simp
          simp only [siteP, siteQ, hk, if_false, hcref, map_mul, Complex.conj_conj, hcr]
          rw [show multDiff Z Z' k * pairWeight (modScaledBump w γ₀) ((k : ℂ).re - 1 / 2) (k : ℂ).im *
              (multDiff Z Z' k * pairWeight (modScaledBump w γ₀) ((k : ℂ).re - 1 / 2) (k : ℂ).im) =
            multDiff Z Z' k * multDiff Z Z' k *
              pairWeight (modScaledBump w γ₀) ((k : ℂ).re - 1 / 2) (k : ℂ).im ^ 2 by ring,
            hQ, ← pow_mul, hcreal]
          rw [show ((multDiff Z Z' k).re : ℂ) * ((multDiff Z Z' k).re : ℂ) =
              (((multDiff Z Z' k).re * (multDiff Z Z' k).re : ℝ) : ℂ) by push_cast; ring,
            Complex.re_ofReal_mul]
          exact mul_nonneg (mul_self_nonneg _) hdark)
    hpos hsum hzero
  -- the pair weight at the height of `t₀` is nonzero
  have hp0 := (hres ⟨t₀, mem_carrier_of_multDiff_ne_zero hct₀, ht₀re⟩).1
  simp only [siteP] at hp0
  exact hct₀ ((mul_eq_zero.mp hp0).resolve_right (pairWeight_modScaledBump_ne_zero hw0 γ₀ _))

/-! ### Explicit scales -/

/-- **The pair gap is quadratic in the depth.** For `|δ| ≤ s`,
`A(2δ) − A(0) ≥ (π² − 8) δ²/(a a'²)`, from `cosh(2δT) ≥ 1 + 2δ²T²` and `a²T² = π²/4`. -/
theorem pairGap_ge {T δ s : ℝ} (hT : 0 < T) (hδ : |δ| ≤ s) :
    (π ^ 2 - 8) * δ ^ 2 / (inghamA T * tiltA T s ^ 2) ≤ pairGap T δ := by
  set a := inghamA T with ha
  have ha0 : 0 < a := by rw [ha, inghamA]; positivity
  have haT : a * T = π / 2 := by rw [ha, inghamA]; field_simp
  have hs : 0 ≤ s := (abs_nonneg δ).trans hδ
  have ha'sq : tiltA T s ^ 2 = a ^ 2 + 4 * s ^ 2 := by
    rw [tiltA, Real.sq_sqrt (by positivity)]
  have hδs : δ ^ 2 ≤ s ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg δ) hδ 2
  have hpg : pairGap T δ = 2 * a * Real.cosh (2 * δ * T) / ((2 * δ) ^ 2 + a ^ 2) - 2 * a / a ^ 2 :=
    rfl
  have hcosh : 1 + (2 * δ * T) ^ 2 / 2 ≤ Real.cosh (2 * δ * T) :=
    _root_.RHTower.DeBruijn.one_add_sq_div_two_le_cosh _
  have hpi : (8 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have ha2T2 : a ^ 2 * T ^ 2 = π ^ 2 / 4 := by rw [← mul_pow, haT]; ring
  have hD : 0 < (2 * δ) ^ 2 + a ^ 2 := by positivity
  have hnum : (π ^ 2 - 8) * δ ^ 2 / 2 ≤ a ^ 2 * Real.cosh (2 * δ * T) - ((2 * δ) ^ 2 + a ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hcosh (sq_nonneg a)
    have e : a ^ 2 * (1 + (2 * δ * T) ^ 2 / 2) = a ^ 2 + 2 * δ ^ 2 * (a ^ 2 * T ^ 2) := by ring
    rw [e, ha2T2] at h
    nlinarith
  rw [hpg, ha'sq]
  calc (π ^ 2 - 8) * δ ^ 2 / (a * (a ^ 2 + 4 * s ^ 2))
      ≤ (π ^ 2 - 8) * δ ^ 2 / (a * ((2 * δ) ^ 2 + a ^ 2)) :=
        div_le_div_of_nonneg_left (mul_nonneg (by linarith) (sq_nonneg δ)) (by positivity)
          (by nlinarith)
    _ ≤ 2 * (a ^ 2 * Real.cosh (2 * δ * T) - ((2 * δ) ^ 2 + a ^ 2)) /
          (a * ((2 * δ) ^ 2 + a ^ 2)) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * a * Real.cosh (2 * δ * T) / ((2 * δ) ^ 2 + a ^ 2) - 2 * a / a ^ 2 := by
        field_simp

/-- **The neighbour tail is quadratic in the scale.** `B' ≤ (4π²/9)(a'/g)²`. -/
theorem tiltB_le {T g s : ℝ} (hT : 0 < T) (hgap : 2 * tiltA T s < g) :
    tiltB T g s ≤ 4 * π ^ 2 / 9 * (tiltA T s ^ 2 / g ^ 2) := by
  have ha'0 : 0 < tiltA T s := Real.sqrt_pos.mpr (by unfold inghamA; positivity)
  set b := g / tiltA T s with hb
  have hb2 : 2 < b := by rw [hb, lt_div_iff₀ ha'0]; linarith
  obtain ⟨hbs, -⟩ := tsum_two_div_sq_sub_one_lt_one hb2
  have hbasel := _root_.RHTower.hasSum_inv_add_one_sq
  have hterm : ∀ n : ℕ, 2 / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) ≤
      8 / (3 * b ^ 2) * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    intro n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hb4 : (4 : ℝ) ≤ b ^ 2 := by nlinarith
    have hn1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    have hx : 4 ≤ b ^ 2 * ((n : ℝ) + 1) ^ 2 := by
      nlinarith [mul_le_mul hb4 hn1 zero_le_one (by positivity)]
    have hpos : 0 < b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1 := by linarith
    calc 2 / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) ≤ 8 / (3 * (b ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
          rw [div_le_div_iff₀ hpos (by positivity)]; nlinarith
      _ = 8 / (3 * b ^ 2) * (((n : ℝ) + 1) ^ 2)⁻¹ := by field_simp
  calc tiltB T g s ≤ ∑' n : ℕ, 8 / (3 * b ^ 2) * (((n : ℝ) + 1) ^ 2)⁻¹ :=
        Summable.tsum_le_tsum hterm hbs (hbasel.summable.mul_left _)
    _ = 8 / (3 * b ^ 2) * (π ^ 2 / 6) := by rw [tsum_mul_left, hbasel.tsum_eq]
    _ = 4 * π ^ 2 / 9 * (tiltA T s ^ 2 / g ^ 2) := by
        rw [hb]
        have hg : 0 < g := by linarith
        field_simp
        ring

/-- **The tilted near-collision constraint.** Let two tempered configurations with different
carriers agree on every `C²` test supported in `[−a, a]`. Let `V < 2a`, `0 < ε ≤ s`, `g > 2a'`
with `(16π²/9) a² a'² cosh(2sV) < (π² − 8) ε² g²`, where `a = π/(2V)` and `a' = √(a² + 4s²)`.
Then the union contains two points of different FE orbits at height distance `< g`, or a point
of depth `> s`, or an off-line point of depth `< ε` in the dark sector of the camera `κ_{a−V/2}`
modulated to the height of a point of the union. -/
theorem exists_near_pair_or_shallow_pair_of_mimic {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') (hne : Z.carrier ≠ Z'.carrier) {a V s g ε : ℝ} (hV : 0 < V)
    (ha : V / 2 < a) (hε : 0 < ε) (hεs : ε ≤ s) (hgap : 2 * tiltA V s < g)
    (hscale : 16 * π ^ 2 / 9 * inghamA V ^ 2 * tiltA V s ^ 2 * Real.cosh (2 * s * V) <
      (π ^ 2 - 8) * ε ^ 2 * g ^ 2)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) :
    (∃ ρ ∈ Z.carrier ∪ Z'.carrier, ∃ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ ∧ ρ' ≠ reflect ρ ∧
        |ρ.im - ρ'.im| < g) ∨
      (∃ ρ ∈ Z.carrier ∪ Z'.carrier, s < |ρ.re - 1 / 2|) ∨
      (∃ ρ ∈ Z.carrier ∪ Z'.carrier, ρ.re ≠ 1 / 2 ∧ |ρ.re - 1 / 2| < ε ∧
        ∃ ρ₀ ∈ Z.carrier ∪ Z'.carrier, InDarkSector (a - V / 2) ρ ρ₀) := by
  by_contra h
  simp only [not_or, not_exists, not_and, not_lt] at h
  obtain ⟨hnear, hdeep, hshallow⟩ := h
  have hs : 0 ≤ s := hε.le.trans hεs
  have hA : 0 < inghamA V := by unfold inghamA; positivity
  have hA' : 0 < tiltA V s := Real.sqrt_pos.mpr (by positivity)
  have hA'sq : tiltA V s ^ 2 = inghamA V ^ 2 + 4 * s ^ 2 := by
    rw [tiltA, Real.sq_sqrt (by positivity)]
  have hg : 0 < g := by linarith
  have hpi : (8 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hpi2 : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  set D₀ := (π ^ 2 - 8) * ε ^ 2 / (inghamA V * tiltA V s ^ 2) with hD₀
  have hD0 : D₀ ≤ 2 / inghamA V := by
    rw [hD₀, div_le_div_iff₀ (by positivity) hA, hA'sq]
    have hεs2 : ε ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hε.le hεs 2
    have h1 : (π ^ 2 - 8) * ε ^ 2 ≤ 2 * (inghamA V ^ 2 + 4 * s ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hpi2.le (sq_nonneg ε), sq_nonneg (inghamA V)]
    linarith [mul_le_mul_of_nonneg_right h1 hA.le]
  have hDpair : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, ρ.re ≠ 1 / 2 → D₀ ≤ pairGap V (ρ.re - 1 / 2) ∨
      ∀ ρ₀ ∈ Z.carrier ∪ Z'.carrier, ¬ InDarkSector (a - V / 2) ρ ρ₀ := by
    intro ρ hρ hre
    by_cases hsh : |ρ.re - 1 / 2| < ε
    · exact Or.inr (hshallow ρ hρ hre hsh)
    refine Or.inl (le_trans ?_ (pairGap_ge hV (hdeep ρ hρ)))
    have hεδ : ε ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
      rw [← sq_abs (ρ.re - 1 / 2)]
      exact pow_le_pow_left₀ hε.le (not_lt.mp hsh) 2
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hεδ (by linarith)) (by positivity)
  have hcosh := Real.cosh_pos (2 * s * V)
  have hR : 2 * (2 * inghamA V * Real.cosh (2 * s * V) / tiltA V s ^ 2 * tiltB V g s) ≤
      16 * π ^ 2 / 9 * inghamA V * Real.cosh (2 * s * V) / g ^ 2 := by
    calc 2 * (2 * inghamA V * Real.cosh (2 * s * V) / tiltA V s ^ 2 * tiltB V g s)
        ≤ 2 * (2 * inghamA V * Real.cosh (2 * s * V) / tiltA V s ^ 2 *
          (4 * π ^ 2 / 9 * (tiltA V s ^ 2 / g ^ 2))) := by
          gcongr
          exact tiltB_le hV hgap
      _ = 16 * π ^ 2 / 9 * inghamA V * Real.cosh (2 * s * V) / g ^ 2 := by
          field_simp
          ring
  have hlt : 16 * π ^ 2 / 9 * inghamA V * Real.cosh (2 * s * V) / g ^ 2 < D₀ := by
    rw [hD₀, div_lt_div_iff₀ (by positivity) (by positivity)]
    calc 16 * π ^ 2 / 9 * inghamA V * Real.cosh (2 * s * V) * (inghamA V * tiltA V s ^ 2)
        = 16 * π ^ 2 / 9 * inghamA V ^ 2 * tiltA V s ^ 2 * Real.cosh (2 * s * V) := by ring
      _ < (π ^ 2 - 8) * ε ^ 2 * g ^ 2 := hscale
  exact hne (eq_of_weil_eq_of_pairSeparated Z Z' hZ hZ' hg hV hs hdeep
    (fun ρ hρ ρ' hρ' h1 h2 => hnear ρ hρ ρ' hρ' h1 h2) hgap hD0 hDpair (by linarith) ha hW).1

/-! ### The dark sector lies where the camera is dim -/

/-- Fourth powers of points within `|x|/8` of a real `x` have nonnegative real part. -/
theorem re_pow_four_nonneg_of_near_real {u : ℂ} {x : ℝ} (h : ‖u - x‖ ≤ |x| / 8) :
    0 ≤ (u ^ 4).re := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    have hu : u = 0 := by simpa using h
    simp [hu]
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  set e : ℂ := (u - x) / x with he
  have hu : u = x * (1 + e) := by rw [he]; field_simp; ring
  have hen : ‖e‖ ≤ 1 / 8 := by
    rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (abs_pos.mpr hx)]
    linarith
  have n1 : ‖(4 : ℂ) * e‖ = 4 * ‖e‖ := by rw [norm_mul]; norm_num
  have n2 : ‖(6 : ℂ) * e ^ 2‖ = 6 * ‖e‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
  have n3 : ‖(4 : ℂ) * e ^ 3‖ = 4 * ‖e‖ ^ 3 := by rw [norm_mul, norm_pow]; norm_num
  have n4 : ‖e ^ 4‖ = ‖e‖ ^ 4 := norm_pow e 4
  have hbound : ‖4 * e + 6 * e ^ 2 + 4 * e ^ 3 + e ^ 4‖ ≤
      4 * ‖e‖ + 6 * ‖e‖ ^ 2 + 4 * ‖e‖ ^ 3 + ‖e‖ ^ 4 := by
    calc ‖4 * e + 6 * e ^ 2 + 4 * e ^ 3 + e ^ 4‖
        ≤ ‖4 * e + 6 * e ^ 2 + 4 * e ^ 3‖ + ‖e ^ 4‖ := norm_add_le _ _
      _ ≤ ‖4 * e + 6 * e ^ 2‖ + ‖(4 : ℂ) * e ^ 3‖ + ‖e ^ 4‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖(4 : ℂ) * e‖ + ‖(6 : ℂ) * e ^ 2‖ + ‖(4 : ℂ) * e ^ 3‖ + ‖e ^ 4‖ := by
          gcongr; exact norm_add_le _ _
      _ = 4 * ‖e‖ + 6 * ‖e‖ ^ 2 + 4 * ‖e‖ ^ 3 + ‖e‖ ^ 4 := by rw [n1, n2, n3, n4]
  set t := ‖e‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg e
  have hre : 1 - (4 * t + 6 * t ^ 2 + 4 * t ^ 3 + t ^ 4) ≤ ((1 + e) ^ 4).re := by
    rw [show (1 + e) ^ 4 = 1 + (4 * e + 6 * e ^ 2 + 4 * e ^ 3 + e ^ 4) by ring, Complex.add_re,
      Complex.one_re]
    have := (abs_le.mp (Complex.abs_re_le_norm (4 * e + 6 * e ^ 2 + 4 * e ^ 3 + e ^ 4))).1
    linarith
  have h2 : t ^ 2 ≤ 1 / 64 := by nlinarith
  have h3 : t ^ 3 ≤ 1 / 512 := by nlinarith
  have h4 : t ^ 4 ≤ 1 / 4096 := by nlinarith
  rw [hu, mul_pow, show (x : ℂ) ^ 4 = ((x ^ 4 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) (by linarith)

theorem abs_exp_sub_one_le (y : ℝ) : |Real.exp y - 1| ≤ Real.exp |y| - 1 := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, abs_of_nonneg (by linarith [Real.one_le_exp hy])]
  · rw [abs_of_nonpos hy, abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr hy])]
    linarith [Real.add_one_le_exp y, Real.add_one_le_exp (-y)]

/-- **Tilt perturbation.** For a continuous window supported in `|u| ≤ r`,
`‖f̂(x − iδ) − f̂(x)‖ ≤ (e^{|δ|r} − 1) ∫ ‖f‖`. -/
theorem norm_paperFT_tilt_sub_le {f : ℝ → ℂ} (hf : Continuous f) {r : ℝ}
    (hfs : ∀ u, f u ≠ 0 → |u| ≤ r) (x δ : ℝ) :
    ‖paperFT f ((x : ℂ) - I * δ) - paperFT f x‖ ≤ (Real.exp (|δ| * r) - 1) * ∫ u, ‖f u‖ := by
  have hfc : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hfs
  have hcont : Continuous (tilt δ f) := hf.mul (by fun_prop)
  have hcomp : HasCompactSupport (tilt δ f) := hfc.mul_right
  rw [paperFT_sub_I_mul_eq_tilt, paperFT_def, paperFT_def,
    ← integral_sub (integrable_mul_cexp hcont hcomp _) (integrable_mul_cexp hf hfc _),
    ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (ae_of_all _ fun u => norm_nonneg _)
    ((hf.norm.integrable_of_hasCompactSupport hfc.norm).const_mul _) (ae_of_all _ fun u => ?_))
  have hE : ‖cexp (I * (x : ℂ) * u)‖ = 1 := by
    rw [show I * (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have e : tilt δ f u * cexp (I * x * u) - f u * cexp (I * x * u) =
      f u * (((Real.exp (δ * u) - 1 : ℝ)) : ℂ) * cexp (I * x * u) := by
    simp only [tilt]; push_cast; ring
  simp only
  rw [e, norm_mul, norm_mul, hE, mul_one, Complex.norm_real, Real.norm_eq_abs]
  by_cases hu : f u = 0
  · rw [hu, norm_zero, zero_mul, mul_zero]
  · have hur := hfs u hu
    have hδu : |δ * u| ≤ |δ| * r := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hur (abs_nonneg δ)
    have : |Real.exp (δ * u) - 1| ≤ Real.exp (|δ| * r) - 1 :=
      (abs_exp_sub_one_le (δ * u)).trans (by linarith [Real.exp_le_exp.mpr hδu])
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

/-- **The dark sector lies where the camera is dim.** The FE pair of `ρ` is outside the dark
sector of `κ_w` at the height of `ρ₀` as soon as `8(e^{|δ|w} − 1)‖κ_w‖₁ ≤ |κ̂_w(γ − γ₀)|`,
`δ = Re ρ − ½`: then `κ̂_w(γ − γ₀ − iδ)` lies within `1/8` of the real number `κ̂_w(γ − γ₀)`. -/
theorem not_inDarkSector_of_bright {w : ℝ} (hw : 0 < w) (ρ ρ₀ : ℂ)
    (hbright : 8 * ((Real.exp (|ρ.re - 1 / 2| * w) - 1) * ∫ u, ‖scaledBump w u‖) ≤
      ‖paperFT (scaledBump w) ((ρ.im - ρ₀.im : ℝ) : ℂ)‖) :
    ¬ InDarkSector w ρ ρ₀ := by
  rw [InDarkSector, not_lt]
  set x := ρ.im - ρ₀.im
  have hreal : paperFT (scaledBump w) (x : ℂ) = ((paperFT (scaledBump w) x).re : ℂ) := by
    have h := conj_paperFT_scaledBump w (x : ℂ)
    rw [Complex.conj_ofReal] at h
    exact (Complex.conj_eq_iff_re.mp h).symm
  have hn : ‖paperFT (scaledBump w) (x : ℂ)‖ = |(paperFT (scaledBump w) x).re| := by
    conv_lhs => rw [hreal]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hpert := norm_paperFT_tilt_sub_le (contDiff_scaledBump w).continuous
    (fun u hu => by
      by_contra h
      exact hu (scaledBump_eq_zero hw (not_le.mp h).le)) x (ρ.re - 1 / 2)
  apply re_pow_four_nonneg_of_near_real (x := (paperFT (scaledBump w) x).re)
  rw [← hreal]
  linarith

/-- **Hiding needs a near-collision, a deep point, or a dim shallow pair.** Under the hypotheses of
`exists_near_pair_or_shallow_pair_of_mimic`, the third alternative can be read off the camera:
an off-line point `ρ` of depth `< ε` and a point `ρ₀` of the union with
`|κ̂_w(γ − γ₀)| < 8(e^{εw} − 1)‖κ_w‖₁`, `w = a − V/2`. So a shallow pair hides only at a height
where the camera transform is dim: near one of its real zeros or in its tail. -/
theorem exists_near_pair_or_dim_shallow_pair_of_mimic {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') (hne : Z.carrier ≠ Z'.carrier) {a V s g ε : ℝ} (hV : 0 < V)
    (ha : V / 2 < a) (hε : 0 < ε) (hεs : ε ≤ s) (hgap : 2 * tiltA V s < g)
    (hscale : 16 * π ^ 2 / 9 * inghamA V ^ 2 * tiltA V s ^ 2 * Real.cosh (2 * s * V) <
      (π ^ 2 - 8) * ε ^ 2 * g ^ 2)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → Z.W f f = Z'.W f f) :
    (∃ ρ ∈ Z.carrier ∪ Z'.carrier, ∃ ρ' ∈ Z.carrier ∪ Z'.carrier, ρ' ≠ ρ ∧ ρ' ≠ reflect ρ ∧
        |ρ.im - ρ'.im| < g) ∨
      (∃ ρ ∈ Z.carrier ∪ Z'.carrier, s < |ρ.re - 1 / 2|) ∨
      (∃ ρ ∈ Z.carrier ∪ Z'.carrier, ρ.re ≠ 1 / 2 ∧ |ρ.re - 1 / 2| < ε ∧
        ∃ ρ₀ ∈ Z.carrier ∪ Z'.carrier, ‖paperFT (scaledBump (a - V / 2)) ((ρ.im - ρ₀.im : ℝ) : ℂ)‖ <
          8 * ((Real.exp (ε * (a - V / 2)) - 1) * ∫ u, ‖scaledBump (a - V / 2) u‖)) := by
  rcases exists_near_pair_or_shallow_pair_of_mimic hZ hZ' hne hV ha hε hεs hgap hscale hW with
    h | h | ⟨ρ, hρ, hre, hsh, ρ₀, hρ₀, hdark⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨ρ, hρ, hre, hsh, ρ₀, hρ₀, ?_⟩)
    have hw : 0 < a - V / 2 := by linarith
    by_contra hdim
    refine not_inDarkSector_of_bright hw ρ ρ₀ (le_trans ?_ (not_lt.mp hdim)) hdark
    have hint : 0 ≤ ∫ u, ‖scaledBump (a - V / 2) u‖ := integral_nonneg fun u => norm_nonneg _
    have hexp : Real.exp (|ρ.re - 1 / 2| * (a - V / 2)) ≤ Real.exp (ε * (a - V / 2)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsh.le hw.le)
    nlinarith

end GaloisForLFunctions.ZeroConfigurationGeometry
