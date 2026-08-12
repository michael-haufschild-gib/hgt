import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCoronaOrderNoGo
import GaloisForLFunctions.HTGeometry.FinitePassiveResponse

/-!
# Subcritical one-subtracted passive response of the Gamma-sewn Stokes current

P-G68 excludes a finite positive unit for the divergent Euler corona.  The Stokes generator itself
supplies a legal replacement.  On prime-power axis `(p,e)`, let its positive gap be

`g_s(p,e) = (e+1) W_s(p)`.

The physical sewn coefficient `b_s(p,e)` obeys `b_s g_s = log(p) p^(-s(e+1))` exactly.  Although
the total physical mass diverges, the one-subtracted atom

`b_s z / (z-g_s) = (b_s g_s) ((z-g_s)⁻¹ + g_s⁻¹)`

is absolutely summable for every upper-half-plane `z` throughout `0<s<1`.  The proof uses the new
lower gap law `g_s >= log(2) p^(1-s)` and a summable majorant
`(log 2)⁻¹ p^(s-2) exp(-s log 2)^e`.  Its countable sum is anti-Herglotz without any Xi divisor,
RH assumption, or imported positivity.  Thus Route P has an unconditional parameter-dependent
passive thermodynamic limit; missing gate is exact completed-Gamma/Xi comparison, not existence of
a source-native passive order.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators Distributions FourierTransform

noncomputable section
namespace RHTower

/-- Positive Stokes frequency on one prime-power axis. -/
def gammaSewnMobiusApertureStokesGap (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  (pk.2 + 1 : ℝ) * gammaSewnMobiusApertureStokesInverseTilt s pk.1

/-- Physical coefficient times Stokes gap is exactly one Euler prime-power intensity. -/
theorem gammaSewnMobiusApertureStokesDualFeatureCoefficient_mul_gap_eq_flux
    {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    ((gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
        gammaSewnMobiusApertureStokesGap s pk : ℝ) : ℂ) =
      primePowerFluxTerm (s : ℂ) pk := by
  have hn : ((pk.2 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hcancel :
      gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
          ((pk.2 + 1 : ℝ) *
            gammaSewnMobiusApertureStokesInverseTilt s pk.1) =
        gammaSewnMobiusApertureStokesInverseTilt s pk.1 *
          (gammaSewnMobiusContinuousApertureFeature s pk.1 pk.2 -
            gammaSewnMobiusContinuousApertureFeature 0 pk.1 pk.2) := by
    rw [gammaSewnMobiusApertureStokesDualFeatureCoefficient,
      gammaSewnMobiusContinuousApertureFeature_zero, sub_zero]
    field_simp [hn]
  rw [gammaSewnMobiusApertureStokesGap, hcancel]
  exact gammaSewnMobiusApertureStokesFluxTerm_eq hs pk

theorem gammaSewnMobiusApertureStokesGap_pos
    {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    0 < gammaSewnMobiusApertureStokesGap s pk := by
  exact mul_pos (by positivity)
    (gammaSewnMobiusApertureStokesInverseTilt_pos hs pk.1)

/-- The inverse tilt grows at least like `p^(1-s)` throughout the positive chamber. -/
theorem gammaSewnMobiusApertureStokesInverseTilt_lower
    {s : ℝ} (hs : 0 < s) (p : Nat.Primes) :
    Real.log 2 * (p : ℝ) ^ (1 - s) ≤
      gammaSewnMobiusApertureStokesInverseTilt s p := by
  let q := xiMobiusContinuousApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode s p
  let c := gammaSewnMobiusValuationContractionMultiplier s p
  let L := Real.log (p : ℝ)
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hp0 : 0 < (p : ℝ) := lt_trans zero_lt_one hp
  have hL : 0 < L := Real.log_pos hp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ L := by
    dsimp only [L]
    apply Real.log_le_log (by norm_num)
    exact_mod_cast p.2.two_le
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos s p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hs p
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos s p
  have hc1 : c ≤ 1 :=
    (gammaSewnMobiusValuationContractionMultiplier_lt_one hs p).le
  have hnode : xiTransversePrimeApertureDiskNode 1 p = q := by
    simp only [q, xiMobiusContinuousApertureDiskNode,
      xiTransversePrimeApertureDiskNode]
    congr 1
    ring
  have hqfrac0 : 0 < q / (1 + q) := by positivity
  have hqfrac : q / (1 + q) ≤ q := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + q)]
    nlinarith
  have hden0 : 0 < c * (q / (1 + q)) * (1 - r) := by positivity
  have hdenle : c * (q / (1 + q)) * (1 - r) ≤ q := by
    calc
      c * (q / (1 + q)) * (1 - r) ≤ 1 * q * 1 := by
        gcongr <;> linarith
      _ = q := by ring
  have hratio : r / q = (p : ℝ) ^ (1 - s) := by
    dsimp only [r, q, xiMobiusContinuousApertureDiskNode]
    rw [← Real.exp_sub]
    rw [Real.rpow_def_of_pos hp0]
    congr 1
    ring
  rw [gammaSewnMobiusApertureStokesInverseTilt]
  rw [hnode]
  change Real.log 2 * (p : ℝ) ^ (1 - s) ≤
    L * r / (c * (q / (1 + q)) * (1 - r))
  rw [← hratio]
  calc
    Real.log 2 * (r / q) ≤ L * (r / q) := by gcongr
    _ = L * r / q := by ring
    _ ≤ L * r / (c * (q / (1 + q)) * (1 - r)) := by
      exact (div_le_div_iff₀ hq0 hden0).2
        (mul_le_mul_of_nonneg_left hdenle (mul_nonneg hL.le hr0.le))

/-- A geometric upper bound for one physical sewn coefficient. -/
theorem gammaSewnMobiusApertureStokesDualFeatureCoefficient_le_geometric
    {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk ≤
      xiMobiusContinuousApertureDiskNode 1 pk.1 *
        xiMobiusContinuousApertureDiskNode s pk.1 ^ pk.2 := by
  let q := xiMobiusContinuousApertureDiskNode 1 pk.1
  let r := xiMobiusContinuousApertureDiskNode s pk.1
  let c := gammaSewnMobiusValuationContractionMultiplier s pk.1
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos 1 pk.1
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos s pk.1
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hs pk.1
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos s pk.1
  have hc1 : c ≤ 1 :=
    (gammaSewnMobiusValuationContractionMultiplier_lt_one hs pk.1).le
  have hnode : xiTransversePrimeApertureDiskNode 1 pk.1 = q := by
    simp only [q, xiMobiusContinuousApertureDiskNode,
      xiTransversePrimeApertureDiskNode]
    congr 1
    ring
  have hqfrac : q / (1 + q) ≤ q := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + q)]
    nlinarith
  rw [gammaSewnMobiusApertureStokesDualFeatureCoefficient,
    gammaSewnMobiusContinuousApertureFeature,
    xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
  rw [hnode]
  change c * (q / (1 + q) * (1 - r) * r ^ pk.2) /
      (pk.2 + 1 : ℝ) ≤ q * r ^ pk.2
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < pk.2 + 1)]
  calc
    c * (q / (1 + q) * (1 - r) * r ^ pk.2)
        ≤ 1 * (q * 1 * r ^ pk.2) := by gcongr <;> linarith
    _ = q * r ^ pk.2 := by ring
    _ ≤ q * r ^ pk.2 * (pk.2 + 1 : ℝ) := by
      nlinarith [mul_nonneg hq0.le (pow_nonneg hr0.le pk.2)]

/-- Product majorant for physical coefficient divided by Stokes gap. -/
def gammaSewnMobiusApertureStokesPassiveMajorant
    (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  (Real.log 2)⁻¹ * (pk.1 : ℝ) ^ (s - 2) *
    Real.exp (-s * Real.log 2) ^ pk.2

theorem gammaSewnMobiusApertureStokesDualFeatureCoefficient_div_gap_le_majorant
    {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk /
        gammaSewnMobiusApertureStokesGap s pk ≤
      gammaSewnMobiusApertureStokesPassiveMajorant s pk := by
  let q := xiMobiusContinuousApertureDiskNode 1 pk.1
  let r := xiMobiusContinuousApertureDiskNode s pk.1
  let L := Real.log (pk.1 : ℝ)
  let R := Real.exp (-s * Real.log 2)
  have hp : (1 : ℝ) < (pk.1 : ℝ) := by exact_mod_cast pk.1.2.one_lt
  have hp0 : 0 < (pk.1 : ℝ) := lt_trans zero_lt_one hp
  have hL : 0 < L := Real.log_pos hp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos 1 pk.1
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos s pk.1
  have hR0 : 0 < R := Real.exp_pos _
  have hR1 : R < 1 := by
    dsimp only [R]
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hrR : r ≤ R := by
    dsimp only [r, R, xiMobiusContinuousApertureDiskNode]
    apply Real.exp_le_exp.mpr
    have hlogle : Real.log 2 ≤ L := by
      dsimp only [L]
      apply Real.log_le_log (by norm_num)
      exact_mod_cast pk.1.2.two_le
    nlinarith
  have hb0 :
      0 ≤ gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk :=
    (gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit hs pk).1
  have hgap0 : 0 < gammaSewnMobiusApertureStokesGap s pk :=
    gammaSewnMobiusApertureStokesGap_pos hs pk
  have hlower0 :
      0 < Real.log 2 * (pk.1 : ℝ) ^ (1 - s) := by positivity
  have hlower :
      Real.log 2 * (pk.1 : ℝ) ^ (1 - s) ≤
        gammaSewnMobiusApertureStokesGap s pk := by
    rw [gammaSewnMobiusApertureStokesGap]
    calc
      Real.log 2 * (pk.1 : ℝ) ^ (1 - s) ≤
          1 * gammaSewnMobiusApertureStokesInverseTilt s pk.1 := by
        simpa using gammaSewnMobiusApertureStokesInverseTilt_lower hs pk.1
      _ ≤ (pk.2 + 1 : ℝ) *
          gammaSewnMobiusApertureStokesInverseTilt s pk.1 := by
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (gammaSewnMobiusApertureStokesInverseTilt_pos hs pk.1).le
  have hfirst :
      gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk /
          gammaSewnMobiusApertureStokesGap s pk ≤
        (q * r ^ pk.2) /
          (Real.log 2 * (pk.1 : ℝ) ^ (1 - s)) := by
    exact div_le_div₀ (mul_nonneg hq0.le (pow_nonneg hr0.le _))
      (gammaSewnMobiusApertureStokesDualFeatureCoefficient_le_geometric hs pk)
      hlower0 hlower
  have hq : q = (pk.1 : ℝ)⁻¹ := by
    dsimp only [q, xiMobiusContinuousApertureDiskNode]
    rw [← Real.rpow_neg_one]
    rw [Real.rpow_def_of_pos hp0]
    congr 1
    ring
  have hreorder :
      (q * r ^ pk.2) /
          (Real.log 2 * (pk.1 : ℝ) ^ (1 - s)) =
        (Real.log 2)⁻¹ * (pk.1 : ℝ) ^ (s - 2) * r ^ pk.2 := by
    rw [hq]
    have hpowne : (pk.1 : ℝ) ^ (1 - s) ≠ 0 := by positivity
    rw [div_eq_mul_inv, mul_inv]
    calc
      (pk.1 : ℝ)⁻¹ * r ^ pk.2 *
          ((Real.log 2)⁻¹ * ((pk.1 : ℝ) ^ (1 - s))⁻¹) =
          (Real.log 2)⁻¹ *
            ((pk.1 : ℝ)⁻¹ * ((pk.1 : ℝ) ^ (1 - s))⁻¹) *
              r ^ pk.2 := by ring
      _ = (Real.log 2)⁻¹ *
            ((pk.1 : ℝ) ^ (-1 : ℝ) * (pk.1 : ℝ) ^ (-(1 - s))) *
              r ^ pk.2 := by
          rw [Real.rpow_neg_one, Real.rpow_neg hp0.le]
      _ = (Real.log 2)⁻¹ * (pk.1 : ℝ) ^ (s - 2) * r ^ pk.2 := by
          rw [← Real.rpow_add hp0]
          congr 2
          ring
  calc
    gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk /
        gammaSewnMobiusApertureStokesGap s pk ≤
      (q * r ^ pk.2) /
        (Real.log 2 * (pk.1 : ℝ) ^ (1 - s)) := hfirst
    _ = (Real.log 2)⁻¹ * (pk.1 : ℝ) ^ (s - 2) * r ^ pk.2 := hreorder
    _ ≤ (Real.log 2)⁻¹ * (pk.1 : ℝ) ^ (s - 2) * R ^ pk.2 := by
      gcongr
    _ = gammaSewnMobiusApertureStokesPassiveMajorant s pk := rfl

/-- The product majorant is summable precisely in the RH-relevant subcritical chamber. -/
theorem summable_gammaSewnMobiusApertureStokesPassiveMajorant
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Summable (gammaSewnMobiusApertureStokesPassiveMajorant s) := by
  let R := Real.exp (-s * Real.log 2)
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hR1 : R < 1 := by
    dsimp only [R]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have he : Summable (fun e : ℕ => R ^ e) :=
    summable_geometric_of_lt_one hR0 hR1
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (s - 2)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hnonneg : ∀ pk : Nat.Primes × ℕ,
      0 ≤ gammaSewnMobiusApertureStokesPassiveMajorant s pk := by
    intro pk
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le) (by positivity)) (by positivity)
  rw [summable_prod_of_nonneg hnonneg]
  constructor
  · intro p
    exact he.mul_left ((Real.log 2)⁻¹ * (p : ℝ) ^ (s - 2))
  · have htsum : ∀ p : Nat.Primes,
        ∑' e : ℕ, gammaSewnMobiusApertureStokesPassiveMajorant s (p, e) =
          ((Real.log 2)⁻¹ * (p : ℝ) ^ (s - 2)) * (1 - R)⁻¹ := by
      intro p
      rw [show (fun e : ℕ => gammaSewnMobiusApertureStokesPassiveMajorant s (p, e)) =
          fun e => ((Real.log 2)⁻¹ * (p : ℝ) ^ (s - 2)) * R ^ e by
        funext e
        rfl]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hR0 hR1]
    apply (hp.mul_left ((Real.log 2)⁻¹ * (1 - R)⁻¹)).congr
    intro p
    rw [htsum]
    ring

theorem summable_gammaSewnMobiusApertureStokesDualFeatureCoefficient_div_gap
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Summable (fun pk =>
      gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk /
        gammaSewnMobiusApertureStokesGap s pk) := by
  exact Summable.of_nonneg_of_le
    (fun pk => div_nonneg
      (gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit hs pk).1
      (gammaSewnMobiusApertureStokesGap_pos hs pk).le)
    (gammaSewnMobiusApertureStokesDualFeatureCoefficient_div_gap_le_majorant hs)
    (summable_gammaSewnMobiusApertureStokesPassiveMajorant hs hs1)

/-- One subtraction at zero of the resolvent of the unbounded positive Stokes generator. -/
def gammaSewnMobiusApertureStokesOneSubtractedAtom
    (s : ℝ) (z : ℂ) (pk : Nat.Primes × ℕ) : ℂ :=
  (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk : ℂ) * z /
    (z - (gammaSewnMobiusApertureStokesGap s pk : ℂ))

theorem norm_gammaSewnMobiusApertureStokesOneSubtractedAtom_le
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im)
    (pk : Nat.Primes × ℕ) :
    ‖gammaSewnMobiusApertureStokesOneSubtractedAtom s z pk‖ ≤
      ‖z‖ * (1 + ‖z‖ / z.im) *
        (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk /
          gammaSewnMobiusApertureStokesGap s pk) := by
  let b := gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk
  let g := gammaSewnMobiusApertureStokesGap s pk
  let d := ‖z - (g : ℂ)‖
  have hb : 0 ≤ b :=
    (gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit hs pk).1
  have hg : 0 < g := gammaSewnMobiusApertureStokesGap_pos hs pk
  have himabs : |(z - (g : ℂ)).im| ≤ d :=
    Complex.abs_im_le_norm _
  have him : z.im ≤ d := by
    simpa [d, abs_of_pos hz] using himabs
  have hd : 0 < d := lt_of_lt_of_le hz him
  have htri0 := norm_sub_le z (z - (g : ℂ))
  have htri : g ≤ d + ‖z‖ := by
    simpa [d, abs_of_pos hg, add_comm] using htri0
  have hzscale : ‖z‖ ≤ (‖z‖ / z.im) * d := by
    calc
      ‖z‖ = (‖z‖ / z.im) * z.im := by field_simp
      _ ≤ (‖z‖ / z.im) * d := by
        exact mul_le_mul_of_nonneg_left him (div_nonneg (norm_nonneg _) hz.le)
  have hgscale : g ≤ (1 + ‖z‖ / z.im) * d := by
    nlinarith
  have hrecip : 1 / d ≤ (1 + ‖z‖ / z.im) / g := by
    rw [div_le_div_iff₀ hd hg]
    simpa using hgscale
  change ‖((b : ℂ) * z / (z - (g : ℂ)))‖ ≤
    ‖z‖ * (1 + ‖z‖ / z.im) * (b / g)
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb]
  change b * ‖z‖ / d ≤ ‖z‖ * (1 + ‖z‖ / z.im) * (b / g)
  calc
    b * ‖z‖ / d = (b * ‖z‖) * (1 / d) := by ring
    _ ≤ (b * ‖z‖) * ((1 + ‖z‖ / z.im) / g) := by
      exact mul_le_mul_of_nonneg_left hrecip (mul_nonneg hb (norm_nonneg _))
    _ = ‖z‖ * (1 + ‖z‖ / z.im) * (b / g) := by ring

/-- Absolute convergence of one-subtracted response at every upper-half-plane point. -/
theorem summable_gammaSewnMobiusApertureStokesOneSubtractedAtom
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : 0 < z.im) :
    Summable (gammaSewnMobiusApertureStokesOneSubtractedAtom s z) := by
  apply Summable.of_norm_bounded
    ((summable_gammaSewnMobiusApertureStokesDualFeatureCoefficient_div_gap hs hs1).mul_left
      (‖z‖ * (1 + ‖z‖ / z.im)))
  exact norm_gammaSewnMobiusApertureStokesOneSubtractedAtom_le hs hz

/-- Algebraic subtraction law before using the exact Euler coefficient identity. -/
theorem gammaSewnMobiusApertureStokesOneSubtractedAtom_eq_subtracted_resolvent
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im)
    (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesOneSubtractedAtom s z pk =
      ((gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
          gammaSewnMobiusApertureStokesGap s pk : ℝ) : ℂ) *
        ((z - (gammaSewnMobiusApertureStokesGap s pk : ℂ))⁻¹ +
          ((gammaSewnMobiusApertureStokesGap s pk : ℂ))⁻¹) := by
  let b := gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk
  let g := gammaSewnMobiusApertureStokesGap s pk
  have hg : g ≠ 0 := (gammaSewnMobiusApertureStokesGap_pos hs pk).ne'
  have hzg : z - (g : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at him
    linarith
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  change (b : ℂ) * z / (z - (g : ℂ)) =
    ((b * g : ℝ) : ℂ) * ((z - (g : ℂ))⁻¹ + ((g : ℂ))⁻¹)
  push_cast
  field_simp [hgc, hzg]
  ring

/-- Each subtracted atom carries the exact von Mangoldt Euler intensity. -/
theorem gammaSewnMobiusApertureStokesOneSubtractedAtom_eq_subtracted_euler_resolvent
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im)
    (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesOneSubtractedAtom s z pk =
      primePowerFluxTerm (s : ℂ) pk *
        ((z - (gammaSewnMobiusApertureStokesGap s pk : ℂ))⁻¹ +
          ((gammaSewnMobiusApertureStokesGap s pk : ℂ))⁻¹) := by
  rw [gammaSewnMobiusApertureStokesOneSubtractedAtom_eq_subtracted_resolvent hs hz,
    gammaSewnMobiusApertureStokesDualFeatureCoefficient_mul_gap_eq_flux hs]

/-- Exact absorptive value of one subtracted Stokes atom. -/
theorem gammaSewnMobiusApertureStokesOneSubtractedAtom_im
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im)
    (pk : Nat.Primes × ℕ) :
    (gammaSewnMobiusApertureStokesOneSubtractedAtom s z pk).im =
      -(gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
          gammaSewnMobiusApertureStokesGap s pk * z.im) /
        Complex.normSq (z - (gammaSewnMobiusApertureStokesGap s pk : ℂ)) := by
  rw [gammaSewnMobiusApertureStokesOneSubtractedAtom_eq_subtracted_resolvent hs hz]
  rw [mul_add, Complex.add_im]
  have hfirst := HTGeometry.im_ofReal_div_sub_ofReal
    (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
      gammaSewnMobiusApertureStokesGap s pk)
    (gammaSewnMobiusApertureStokesGap s pk) z
  rw [show
      (((gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
          gammaSewnMobiusApertureStokesGap s pk : ℝ) : ℂ) *
        (z - (gammaSewnMobiusApertureStokesGap s pk : ℂ))⁻¹) =
        (((gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
          gammaSewnMobiusApertureStokesGap s pk : ℝ) : ℂ) /
        (z - (gammaSewnMobiusApertureStokesGap s pk : ℂ))) by rw [div_eq_mul_inv]]
  rw [hfirst]
  have hg : gammaSewnMobiusApertureStokesGap s pk ≠ 0 :=
    (gammaSewnMobiusApertureStokesGap_pos hs pk).ne'
  simp [hg]

theorem gammaSewnMobiusApertureStokesOneSubtractedAtom_im_nonpos
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im)
    (pk : Nat.Primes × ℕ) :
    (gammaSewnMobiusApertureStokesOneSubtractedAtom s z pk).im ≤ 0 := by
  rw [gammaSewnMobiusApertureStokesOneSubtractedAtom_im hs hz]
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg
      (mul_nonneg
        (gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit hs pk).1
        (gammaSewnMobiusApertureStokesGap_pos hs pk).le)
      hz.le))
    (Complex.normSq_nonneg _)

/-- Countable one-subtracted response of physical sewn current against its Stokes generator. -/
def gammaSewnMobiusApertureStokesOneSubtractedResponse
    (s : ℝ) (z : ℂ) : ℂ :=
  ∑' pk : Nat.Primes × ℕ,
    gammaSewnMobiusApertureStokesOneSubtractedAtom s z pk

/-- **Subcritical source passivity.** The countable response is anti-Herglotz for every `0<s<1`. -/
theorem gammaSewnMobiusApertureStokesOneSubtractedResponse_im_nonpos
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {z : ℂ} (hz : 0 < z.im) :
    (gammaSewnMobiusApertureStokesOneSubtractedResponse s z).im ≤ 0 := by
  rw [gammaSewnMobiusApertureStokesOneSubtractedResponse]
  rw [Complex.im_tsum
    (summable_gammaSewnMobiusApertureStokesOneSubtractedAtom hs hs1 hz)]
  exact tsum_nonpos
    (gammaSewnMobiusApertureStokesOneSubtractedAtom_im_nonpos hs hz)

end RHTower
