import GaloisForLFunctions.BiScaleUncertainty.SignedGridEnergySources
import GaloisForLFunctions.BiScaleUncertainty.SeparatedCopyCycleCharge
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Quantitative closed-cycle recovery with signed logarithmic observations

The singular energy bound produces an explicit positive origin collar and
continuity modulus. Two literal closed products then recover each signed
correlation value with an explicit noise bound. A finite mesh extends this to
an entire bounded window; actual signed logarithmic samples control the tail.

For a fixed energy ceiling and accuracy, the mesh size, maximum cycle order,
and amplification factor are explicit and independent of the source. On each
fixed signed-grid fibre, this gives uniform finite-accuracy reconstruction.
This positive theorem does not assert a uniform order for exact recovery.
-/

open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle

noncomputable section
set_option autoImplicit false
variable {K : ℝ}

/-- The actual closed product, normalized separately at each edge. -/
def value (f : LevyEnergySource K) (l : List ℝ) : ℝ :=
  if l.sum = 0 then (l.map f.correlation).prod else 0

theorem value_eq_normalized (f : LevyEnergySource K) (l : List ℝ) :
    value f l = SeparatedCycle.closedProduct f.source l /
      autocorr f.source 0 ^ l.length := by
  have hp : (l.map f.correlation).prod =
      (l.map (autocorr f.source)).prod / autocorr f.source 0 ^ l.length := by
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, ih,
        LevyEnergySource.correlation, pow_succ]
      ring
  simp only [value, SeparatedCycle.closedProduct, SeparatedCycle.rawProduct]
  split_ifs <;> simp_all

def spoke (n : ℕ) (x : ℝ) : List ℝ :=
  (-x) :: List.replicate (n + 1) (x / ((n : ℝ) + 1))

theorem spoke_sum (n : ℕ) (x : ℝ) : (spoke n x).sum = 0 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [spoke, List.sum_cons, List.sum_replicate, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp
  ring

theorem spoke_length (n : ℕ) (x : ℝ) : (spoke n x).length = n + 2 := by
  simp [spoke]

theorem value_pair (f : LevyEnergySource K) (x : ℝ) :
    value f [x, -x] = f.correlation x ^ 2 := by
  simp [value, pow_two]

theorem value_spoke (f : LevyEnergySource K) (n : ℕ) (x : ℝ) :
    value f (spoke n x) =
      f.correlation x * f.correlation (x / ((n : ℝ) + 1)) ^ (n + 1) := by
  rw [value, if_pos (spoke_sum n x)]
  simp [spoke]

/-- Explicit radius for the singular-energy continuity estimate. -/
def continuityRadius (K ε : ℝ) : ℝ :=
  Real.exp (-(1 + 8 * max K 0 / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2)))

theorem continuityRadius_pos (K ε : ℝ) : 0 < continuityRadius K ε :=
  Real.exp_pos _

theorem correlation_close (f : LevyEnergySource K) {ε x y : ℝ} (hε : 0 < ε)
    (hxy : |x - y| < continuityRadius K ε) :
    |f.correlation x - f.correlation y| < ε := by
  let c := Real.exp (-(1 / 2 : ℝ))
  have hc : 0 < c := Real.exp_pos _
  have hd : 0 < c * ε ^ 2 := mul_pos hc (sq_pos_of_pos hε)
  let q := 1 + 8 * max K 0 / (c * ε ^ 2)
  have hq : 0 < q := by
    have hn := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8)
      (le_max_right K 0)) hd.le
    dsimp only [q]
    linarith only [hn]
  by_cases heq : x = y
  · simpa only [heq, sub_self, abs_zero] using hε
  have hp : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr heq)
  have hexp : |x - y| < Real.exp (-q) := hxy
  have h1 : |x - y| ≤ 1 := hexp.le.trans
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hq.le))
  have hl := Real.log_lt_log hp hexp
  rw [Real.log_exp] at hl
  have hb := normalized_autocorr_difference_sq_mul_log_le
    f.smooth f.source.hasCompactSupport f.mass_pos hp h1
  change c * (-Real.log |x - y|) *
    (f.correlation x - f.correlation y) ^ 2 ≤ 8 * normalizedArchEnergy f.source at hb
  have hE := f.energy_le.trans (le_max_left K 0)
  have hqeq : q * (c * ε ^ 2) = c * ε ^ 2 + 8 * max K 0 := by
    dsimp only [q]
    field_simp
  by_contra hn
  have he : ε ≤ |f.correlation x - f.correlation y| := le_of_not_gt hn
  have hs : ε ^ 2 ≤ (f.correlation x - f.correlation y) ^ 2 := by
    nlinarith only [he, hε, sq_abs (f.correlation x - f.correlation y)]
  have hw : 0 ≤ c * (-Real.log |x - y|) :=
    mul_nonneg hc.le (by linarith only [hl, hq])
  have hm := mul_le_mul_of_nonneg_left hs hw
  have hstrict := mul_lt_mul_of_pos_right
    (show q < -Real.log |x - y| by linarith only [hl]) hd
  nlinarith only [hb, hE, hm, hstrict, hqeq, hd]

def collarRadius (K : ℝ) : ℝ := continuityRadius K (1 / 2)

theorem collar_pos (K : ℝ) : 0 < collarRadius K := continuityRadius_pos _ _

theorem correlation_collar (f : LevyEnergySource K) {x : ℝ}
    (hx : |x| < collarRadius K) : 1 / 2 < f.correlation x := by
  have h := correlation_close f (x := x) (y := 0) (by norm_num : (0 : ℝ) < 1 / 2)
    (by simpa only [sub_zero, collarRadius] using hx)
  rw [f.correlation_zero] at h
  linarith only [(abs_lt.mp h).1]

private theorem power_difference_bound {u v : ℝ} (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (n : ℕ) : |u ^ n - v ^ n| ≤ (n : ℝ) * |u - v| := by
  have hmax : 0 ≤ max |u| |v| := (abs_nonneg u).trans (le_max_left _ _)
  have hp : max |u| |v| ^ (n - 1) ≤ (1 : ℝ) := by
    simpa only [one_pow] using pow_le_pow_left₀ hmax (max_le hu hv) (n - 1)
  calc
    _ ≤ |u - v| * (n : ℝ) * max |u| |v| ^ (n - 1) := abs_pow_sub_pow_le u v n
    _ ≤ |u - v| * (n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by ring

private theorem scalar_recovery {a b u v : ℝ} (hu : 1 / 2 ≤ u) (hv : 1 / 2 ≤ v)
    (hu1 : |u| ≤ 1) (hv1 : |v| ≤ 1) (hb : |b| ≤ 1) (n : ℕ) :
    |a - b| ≤ (2 : ℝ) ^ n * (|a * u ^ n - b * v ^ n| +
      (n : ℝ) * |u ^ 2 - v ^ 2|) := by
  have hs : |u - v| ≤ |u ^ 2 - v ^ 2| := by
    calc
      _ ≤ |u - v| * (u + v) := by
        nlinarith only [hu, hv, abs_nonneg (u - v)]
      _ = |u ^ 2 - v ^ 2| := by
        rw [← abs_of_nonneg (show 0 ≤ u + v by linarith only [hu, hv]), ← abs_mul]
        congr 1
        ring
  have hp := (power_difference_bound hu1 hv1 n).trans
    (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n))
  have hu0 : 0 ≤ u := by linarith only [hu]
  have hlow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hu n
  have hbound : (1 / 2 : ℝ) ^ n * |a - b| ≤
      |a * u ^ n - b * v ^ n| + (n : ℝ) * |u ^ 2 - v ^ 2| := by
    calc
      _ ≤ u ^ n * |a - b| := mul_le_mul_of_nonneg_right hlow (abs_nonneg _)
      _ = |(a * u ^ n - b * v ^ n) + b * (v ^ n - u ^ n)| := by
        rw [show (a * u ^ n - b * v ^ n) + b * (v ^ n - u ^ n) =
          u ^ n * (a - b) by ring, abs_mul, abs_of_nonneg (pow_nonneg hu0 n)]
      _ ≤ |a * u ^ n - b * v ^ n| + |b * (v ^ n - u ^ n)| := abs_add_le _ _
      _ ≤ |a * u ^ n - b * v ^ n| + |u ^ n - v ^ n| := by
        rw [abs_mul, abs_sub_comm (v ^ n)]
        exact add_le_add le_rfl (by nlinarith only [hb, abs_nonneg (u ^ n - v ^ n)])
      _ ≤ _ := add_le_add le_rfl hp
  have hscale := mul_le_mul_of_nonneg_left hbound (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  have hinv : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  simpa only [← mul_assoc, hinv, one_mul] using hscale

/-- Two literal closed cycles recover a signed outer value from an energy-proved collar. -/
theorem correlation_recovery (f g : LevyEnergySource K) (n : ℕ) (x : ℝ)
    (hx : |x / ((n : ℝ) + 1)| < collarRadius K) :
    |f.correlation x - g.correlation x| ≤ (2 : ℝ) ^ (n + 1) *
      (|value f (spoke n x) - value g (spoke n x)| + ((n : ℝ) + 1) *
        |value f [x / ((n : ℝ) + 1), -(x / ((n : ℝ) + 1))] -
          value g [x / ((n : ℝ) + 1), -(x / ((n : ℝ) + 1))]|) := by
  simp only [value_spoke, value_pair]
  simpa only [Nat.cast_add, Nat.cast_one] using scalar_recovery
    (correlation_collar f hx).le (correlation_collar g hx).le
    (f.abs_correlation_le_one _) (g.abs_correlation_le_one _)
    (g.abs_correlation_le_one x) (n + 1)

/-- Number of extra subdivisions needed to place every inner lag in the energy collar. -/
def depth (K L : ℝ) : ℕ := ⌈|L| / collarRadius K⌉₊

theorem subdivision_in_collar (K L x : ℝ) (hx : |x| ≤ |L|) :
    |x / ((depth K L : ℝ) + 1)| < collarRadius K := by
  have hr := collar_pos K
  have hc : |L| / collarRadius K ≤ (depth K L : ℝ) := Nat.le_ceil _
  have hm := (div_le_iff₀ hr).mp hc
  have hn : 0 < (depth K L : ℝ) + 1 := by positivity
  rw [abs_div, abs_of_pos hn]
  apply (div_lt_iff₀ hn).mpr
  nlinarith only [hm, hx, hr]

/-- A source-independent subdivision count turns the two closed observations into a
quantitative signed reconstruction on the whole chosen window. -/
theorem window_recovery (f g : LevyEnergySource K) (L x : ℝ) (hx : |x| ≤ |L|) :
    let n := depth K L
    let y := x / ((n : ℝ) + 1)
    |f.correlation x - g.correlation x| ≤ (2 : ℝ) ^ (n + 1) *
      (|value f (spoke n x) - value g (spoke n x)| + ((n : ℝ) + 1) *
        |value f [y, -y] - value g [y, -y]|) :=
  correlation_recovery f g _ x (subdivision_in_collar K L x hx)

/-- Every lag has an explicit finite reconstruction protocol, without an assumed collar. -/
theorem point_recovery (f g : LevyEnergySource K) (x : ℝ) :
    let n := depth K x
    let y := x / ((n : ℝ) + 1)
    |f.correlation x - g.correlation x| ≤ (2 : ℝ) ^ (n + 1) *
      (|value f (spoke n x) - value g (spoke n x)| + ((n : ℝ) + 1) *
        |value f [y, -y] - value g [y, -y]|) := window_recovery f g x x le_rfl

/-- Explicit radius beyond which signed logarithmic sampling has error below ε. -/
def samplingRadius (K ε : ℝ) : ℝ :=
  1 + 8 * max K 0 / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2)

theorem samplingRadius_pos (K ε : ℝ) : 0 < samplingRadius K ε := by
  have hn : 0 ≤ 8 * max K 0 / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2) := by positivity
  unfold samplingRadius
  linarith only [hn]

theorem signed_sample_close (f : LevyEnergySource K) {ε T : ℝ} (hε : 0 < ε)
    (hT : samplingRadius K ε ≤ T) :
    |f.correlation T - f.correlation (Real.log (logarithmicCeilNode T : ℝ))| < ε := by
  let c := Real.exp (-(1 / 2 : ℝ))
  have hc : 0 < c := Real.exp_pos _
  have hd : 0 < c * ε ^ 2 := mul_pos hc (sq_pos_of_pos hε)
  have hTp : 0 < T := (samplingRadius_pos K ε).trans_le hT
  have hAe : samplingRadius K ε * (c * ε ^ 2) = c * ε ^ 2 + 8 * max K 0 := by
    unfold samplingRadius
    dsimp only [c]
    field_simp
  have hb := f.signed_sample_error_sq_le hTp.le
  change c * T * (f.correlation T -
    f.correlation (Real.log (logarithmicCeilNode T : ℝ))) ^ 2 ≤ 8 * K at hb
  by_contra hn
  have he := le_of_not_gt hn
  have hs : ε ^ 2 ≤ (f.correlation T -
      f.correlation (Real.log (logarithmicCeilNode T : ℝ))) ^ 2 := by
    nlinarith only [he, hε, sq_abs (f.correlation T -
      f.correlation (Real.log (logarithmicCeilNode T : ℝ)))]
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hc.le hTp.le)
  have hAT := mul_le_mul_of_nonneg_right hT hd.le
  have hK := le_max_left K 0
  nlinarith only [hb, hm, hAT, hAe, hd, hK]

/-- Signed grid values control the remote comparison; no grid value is discarded. -/
theorem signed_tail_comparison (f g : LevyEnergySource K) {ε : ℝ} (hε : 0 < ε)
    (x : ℝ) (hx : samplingRadius K ε ≤ |x|) :
    |f.correlation x - g.correlation x| <
      |f.correlation (Real.log (logarithmicCeilNode |x| : ℝ)) -
        g.correlation (Real.log (logarithmicCeilNode |x| : ℝ))| + 2 * ε := by
  have hf := signed_sample_close f hε hx
  have hg := signed_sample_close g hε hx
  rw [f.correlation_abs] at hf
  rw [g.correlation_abs] at hg
  let z := Real.log (logarithmicCeilNode |x| : ℝ)
  have htriangle : |f.correlation x - g.correlation x| ≤
      |f.correlation x - f.correlation z| + |f.correlation z - g.correlation z| +
        |g.correlation x - g.correlation z| := by
    calc
      _ = |(f.correlation x - f.correlation z) + (f.correlation z - g.correlation z) -
          (g.correlation x - g.correlation z)| := by congr 1; ring
      _ ≤ |(f.correlation x - f.correlation z) + (f.correlation z - g.correlation z)| +
          |g.correlation x - g.correlation z| := abs_sub _ _
      _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
  dsimp only [z] at htriangle
  linarith only [htriangle, hf, hg]

/-- A uniform mesh of a bounded real interval, with an explicit cardinality. -/
abbrev meshLength (R δ : ℝ) : ℕ := ⌊2 * R / δ⌋₊ + 1

def meshPoint (R δ : ℝ) (i : Fin (meshLength R δ)) : ℝ := -R + δ * (i : ℕ)

theorem meshPoint_mem {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (i : Fin (meshLength R δ)) : |meshPoint R δ i| ≤ R := by
  have hi : (i : ℕ) ≤ ⌊2 * R / δ⌋₊ := by have := i.isLt; unfold meshLength at this; omega
  have hic : ((i : ℕ) : ℝ) ≤ (⌊2 * R / δ⌋₊ : ℝ) := by exact_mod_cast hi
  have hf : (⌊2 * R / δ⌋₊ : ℝ) ≤ 2 * R / δ := Nat.floor_le (by positivity)
  have hu := (le_div_iff₀ hδ).mp (hic.trans hf)
  have hl := mul_nonneg hδ.le (Nat.cast_nonneg (i : ℕ))
  unfold meshPoint
  rw [abs_le]
  constructor <;> nlinarith only [hu, hl]

theorem mesh_covers {R δ x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ R) :
    ∃ i : Fin (meshLength R δ), |x - meshPoint R δ i| < δ := by
  have hxl := (abs_le.mp hx).1
  have hxu := (abs_le.mp hx).2
  have hq : 0 ≤ (x + R) / δ := div_nonneg (by linarith only [hxl]) hδ.le
  have hi : ⌊(x + R) / δ⌋₊ ≤ ⌊2 * R / δ⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right (by linarith only [hxu]) hδ.le)
  let i : Fin (meshLength R δ) := ⟨⌊(x + R) / δ⌋₊, by unfold meshLength; omega⟩
  refine ⟨i, ?_⟩
  have hl := (le_div_iff₀ hδ).mp (Nat.floor_le hq)
  have hu := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((x + R) / δ))
  change |x - (-R + δ * (⌊(x + R) / δ⌋₊ : ℝ))| < δ
  rw [abs_of_nonneg (by nlinarith only [hl])]
  nlinarith only [hu]

/-- Largest error in the two prescribed closed observations at each mesh point. -/
def observationError (f g : LevyEnergySource K) (ε : ℝ) : ℝ :=
  let R := samplingRadius K (ε / 2)
  let δ := continuityRadius K (ε / 2)
  let n := depth K R
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (meshLength R δ) =>
    let x := meshPoint R δ i
    let y := x / ((n : ℝ) + 1)
    max |value f (spoke n x) - value g (spoke n x)|
      |value f [y, -y] - value g [y, -y]|)

theorem observation_le (f g : LevyEnergySource K) (ε : ℝ)
    (i : Fin (meshLength (samplingRadius K (ε / 2)) (continuityRadius K (ε / 2)))) :
    let R := samplingRadius K (ε / 2)
    let n := depth K R
    let x := meshPoint R (continuityRadius K (ε / 2)) i
    let y := x / ((n : ℝ) + 1)
    |value f (spoke n x) - value g (spoke n x)| ≤ observationError f g ε ∧
      |value f [y, -y] - value g [y, -y]| ≤ observationError f g ε := by
  dsimp only
  have h := Finset.le_sup' (s := Finset.univ)
    (fun j : Fin (meshLength (samplingRadius K (ε / 2)) (continuityRadius K (ε / 2))) =>
      let n := depth K (samplingRadius K (ε / 2))
      let x := meshPoint (samplingRadius K (ε / 2)) (continuityRadius K (ε / 2)) j
      let y := x / ((n : ℝ) + 1)
      max |value f (spoke n x) - value g (spoke n x)|
        |value f [y, -y] - value g [y, -y]|) (Finset.mem_univ i)
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

def amplification (K ε : ℝ) : ℝ :=
  let n := depth K (samplingRadius K (ε / 2))
  (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 2)

theorem mesh_recovery (f g : LevyEnergySource K) (ε : ℝ)
    (i : Fin (meshLength (samplingRadius K (ε / 2)) (continuityRadius K (ε / 2)))) :
    let x := meshPoint (samplingRadius K (ε / 2)) (continuityRadius K (ε / 2)) i
    |f.correlation x - g.correlation x| ≤ amplification K ε * observationError f g ε := by
  let R := samplingRadius K (ε / 2)
  let δ := continuityRadius K (ε / 2)
  let n := depth K R
  let x := meshPoint R δ i
  have hx : |x| ≤ |R| := by
    rw [abs_of_pos (samplingRadius_pos K (ε / 2))]
    exact meshPoint_mem (samplingRadius_pos K (ε / 2)).le (continuityRadius_pos K _) i
  have hr := window_recovery f g R x hx
  have ho := observation_le f g ε i
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hp : 0 ≤ (2 : ℝ) ^ (n + 1) := by positivity
  change |f.correlation x - g.correlation x| ≤ _
  calc
    _ ≤ (2 : ℝ) ^ (n + 1) *
        (|value f (spoke n x) - value g (spoke n x)| + ((n : ℝ) + 1) *
          |value f [x / ((n : ℝ) + 1), -(x / ((n : ℝ) + 1))] -
            value g [x / ((n : ℝ) + 1), -(x / ((n : ℝ) + 1))]|) := hr
    _ ≤ (2 : ℝ) ^ (n + 1) *
        (observationError f g ε + ((n : ℝ) + 1) * observationError f g ε) :=
      mul_le_mul_of_nonneg_left
        (add_le_add ho.1 (mul_le_mul_of_nonneg_left ho.2 hn)) hp
    _ = amplification K ε * observationError f g ε := by unfold amplification; dsimp only [n, R]; ring

/-- Finitely many noisy closed products control the entire bounded observation window. -/
theorem finite_window_recovery (f g : LevyEnergySource K) {ε x : ℝ} (hε : 0 < ε)
    (hx : |x| ≤ samplingRadius K (ε / 2)) :
    |f.correlation x - g.correlation x| <
      amplification K ε * observationError f g ε + ε := by
  obtain ⟨i, hi⟩ := mesh_covers (continuityRadius_pos K (ε / 2)) hx
  let z := meshPoint (samplingRadius K (ε / 2)) (continuityRadius K (ε / 2)) i
  have hf := correlation_close f (by linarith only [hε] : 0 < ε / 2) hi
  have hg := correlation_close g (by linarith only [hε] : 0 < ε / 2) hi
  have hm := mesh_recovery f g ε i
  have ht : |f.correlation x - g.correlation x| ≤
      |f.correlation x - f.correlation z| + |f.correlation z - g.correlation z| +
        |g.correlation x - g.correlation z| := by
    calc
      _ = |(f.correlation x - f.correlation z) + (f.correlation z - g.correlation z) -
          (g.correlation x - g.correlation z)| := by congr 1; ring
      _ ≤ |(f.correlation x - f.correlation z) + (f.correlation z - g.correlation z)| +
          |g.correlation x - g.correlation z| := abs_sub _ _
      _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
  dsimp only [z] at ht
  linarith only [ht, hf, hg, hm]

/-- Supremum of the signed logarithmic trace discrepancies, including every node. -/
def traceError (f g : LevyEnergySource K) : ℝ :=
  sSup (Set.range fun n : ℕ => |f.correlation (Real.log n) - g.correlation (Real.log n)|)

private theorem trace_bdd (f g : LevyEnergySource K) :
    BddAbove (Set.range fun n : ℕ =>
      |f.correlation (Real.log n) - g.correlation (Real.log n)|) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hf := f.abs_correlation_le_one (Real.log n)
  have hg := g.abs_correlation_le_one (Real.log n)
  exact (abs_sub _ _).trans (by linarith only [hf, hg])

theorem trace_le (f g : LevyEnergySource K) (n : ℕ) :
    |f.correlation (Real.log n) - g.correlation (Real.log n)| ≤ traceError f g :=
  le_csSup (trace_bdd f g) ⟨n, rfl⟩

theorem traceError_nonneg (f g : LevyEnergySource K) : 0 ≤ traceError f g :=
  (abs_nonneg _).trans (trace_le f g 0)

/-- Global signed recovery: a finite cycle mesh and the actual full signed grid trace.
All radii, cycle orders and mesh cardinalities are explicit functions of K and ε. -/
theorem global_recovery (f g : LevyEnergySource K) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |f.correlation x - g.correlation x| <
      max (amplification K ε * observationError f g ε) (traceError f g) + ε := by
  by_cases hx : |x| ≤ samplingRadius K (ε / 2)
  · exact (finite_window_recovery f g hε hx).trans_le
      (add_le_add (le_max_left _ _) le_rfl)
  · have ht := signed_tail_comparison f g (by linarith only [hε] : 0 < ε / 2) x
      (le_of_not_ge hx)
    have hs := trace_le f g (logarithmicCeilNode |x|)
    have hm := le_max_right (amplification K ε * observationError f g ε) (traceError f g)
    linarith only [ht, hs, hm]

theorem traceError_eq_zero_of_grid_eq (f g : LevyEnergySource K)
    (hgrid : ∀ n : ℕ, f.correlation (Real.log n) = g.correlation (Real.log n)) :
    traceError f g = 0 := by
  apply le_antisymm ?_ (traceError_nonneg f g)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨n, rfl⟩
  simp only [hgrid n, sub_self, abs_zero, le_refl]

/-- On every fixed signed-grid fibre, finitely many closed products recover to any
prescribed accuracy, uniformly over the entire energy-bounded source class. -/
theorem fixed_grid_recovery (f g : LevyEnergySource K) {ε : ℝ} (hε : 0 < ε)
    (hgrid : ∀ n : ℕ, f.correlation (Real.log n) = g.correlation (Real.log n))
    (hobs : observationError f g ε = 0) (x : ℝ) :
    |f.correlation x - g.correlation x| < ε := by
  have h := global_recovery f g hε x
  simpa only [hobs, traceError_eq_zero_of_grid_eq f g hgrid, mul_zero, max_self,
    zero_add] using h

/-- Nodes zero and one carry the common normalized origin value automatically. -/
theorem fixed_integer_grid_recovery (f g : LevyEnergySource K) {ε : ℝ} (hε : 0 < ε)
    (hgrid : ∀ n : ℕ, 2 ≤ n → f.correlation (Real.log n) = g.correlation (Real.log n))
    (hobs : observationError f g ε = 0) (x : ℝ) :
    |f.correlation x - g.correlation x| < ε := by
  apply fixed_grid_recovery f g hε ?_ hobs x
  intro n
  by_cases hn : 2 ≤ n
  · exact hgrid n hn
  · have hn' : n ≤ 1 := by omega
    interval_cases n <;> simp

end
end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
