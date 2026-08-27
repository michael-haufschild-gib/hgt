import GaloisForLFunctions.RHTower.ReflectedBiHeatThetaFinitePartWallSchwarz
import GaloisForLFunctions.RHTower.GammaJumpMultiplier

/-!
# Neutral-height transversality of the reflected bi-heat finite part

The canonical theta-pole finite part has an exact paired sine expansion on
every vertical line `z = sigma + i gamma` in the critical strip.  Its height
derivative at `gamma = 0` is an absolutely summable Gaussian lattice series.
Every atom, and hence the complete derivative, has the strict sign of
`sigma - 1/2`.  Thus the imaginary finite-part channel crosses zero
transversally at neutral height away from the critical wall, with an exact
local orientation and no hypotheses beyond admissibility of the heat datum.
-/

open Complex Filter Set Topology
open scoped BigOperators

noncomputable section

namespace RHTower

theorem ofReal_cpow_re_add_mul_I_im
    {r sigma gamma : ℝ} (hr : 0 < r) :
    (((r : ℂ) ^ ((sigma : ℂ) + (gamma : ℂ) * I))).im =
      r ^ sigma * Real.sin (gamma * Real.log r) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    ← Complex.ofReal_log hr.le, Complex.exp_im]
  simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, mul_one, add_zero]
  rw [Real.rpow_def_of_pos hr]
  congr 2 <;> ring

theorem complementary_cpow_upper_eq
    {N r : ℝ} (hN : 0 < N) (hr : 0 < r) (z : ℂ) :
    ((((N * r : ℝ) : ℂ) ^ (-z)) *
        ((N : ℂ) ^ (-(1 - z)))) =
      (((1 / N : ℝ) : ℂ) * ((r : ℂ) ^ (-z))) := by
  rw [Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hN.le hr.le]
  calc
    (((N : ℂ) ^ (-z) * (r : ℂ) ^ (-z)) *
        (N : ℂ) ^ (-(1 - z))) =
        (((N : ℂ) ^ (-z) * (N : ℂ) ^ (-(1 - z))) *
          (r : ℂ) ^ (-z)) := by ring
    _ = ((N : ℂ) ^ ((-z) + (-(1 - z))) *
          (r : ℂ) ^ (-z)) := by
      rw [Complex.cpow_add]
      exact Complex.ofReal_ne_zero.mpr hN.ne'
    _ = (((1 / N : ℝ) : ℂ) * ((r : ℂ) ^ (-z))) := by
      rw [show (-z) + (-(1 - z)) = (-1 : ℂ) by ring,
        Complex.cpow_neg_one]
      simp [one_div]

theorem complementary_cpow_lower_eq
    {N r : ℝ} (hN : 0 < N) (hr : 0 < r) (z : ℂ) :
    (((N : ℂ) ^ (-z) *
        (((N * r : ℝ) : ℂ) ^ (-(1 - z)))) =
      (((1 / N : ℝ) : ℂ) * ((r : ℂ) ^ (z - 1)))) := by
  rw [Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hN.le hr.le]
  calc
    ((N : ℂ) ^ (-z) *
        ((N : ℂ) ^ (-(1 - z)) * (r : ℂ) ^ (-(1 - z)))) =
        (((N : ℂ) ^ (-z) * (N : ℂ) ^ (-(1 - z))) *
          (r : ℂ) ^ (-(1 - z))) := by ring
    _ = ((N : ℂ) ^ ((-z) + (-(1 - z))) *
          (r : ℂ) ^ (-(1 - z))) := by
      rw [Complex.cpow_add]
      exact Complex.ofReal_ne_zero.mpr hN.ne'
    _ = (((1 / N : ℝ) : ℂ) * ((r : ℂ) ^ (z - 1))) := by
      rw [show (-z) + (-(1 - z)) = (-1 : ℂ) by ring,
        show -(1 - z) = z - 1 by ring, Complex.cpow_neg_one]
      simp [one_div]

theorem complementary_cpow_upper_im
    {N r sigma gamma : ℝ} (hN : 0 < N) (hr : 0 < r) :
    ((((N * r : ℝ) : ℂ) ^
          (-((sigma : ℂ) + (gamma : ℂ) * I)) *
        (N : ℂ) ^ (-(1 - ((sigma : ℂ) + (gamma : ℂ) * I)))).im) =
      -(1 / N * r ^ (-sigma) *
        Real.sin (gamma * Real.log r)) := by
  rw [complementary_cpow_upper_eq hN hr,
    mul_im]
  simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
  rw [show -((sigma : ℂ) + (gamma : ℂ) * I) =
      ((-sigma : ℝ) : ℂ) + ((-gamma : ℝ) : ℂ) * I by
        push_cast
        ring,
    ofReal_cpow_re_add_mul_I_im hr]
  rw [show -gamma * Real.log r = -(gamma * Real.log r) by ring,
    Real.sin_neg]
  ring

theorem complementary_cpow_lower_im
    {N r sigma gamma : ℝ} (hN : 0 < N) (hr : 0 < r) :
    (((N : ℂ) ^ (-((sigma : ℂ) + (gamma : ℂ) * I)) *
        (((N * r : ℝ) : ℂ) ^
          (-(1 - ((sigma : ℂ) + (gamma : ℂ) * I))))).im) =
      1 / N * r ^ (sigma - 1) *
        Real.sin (gamma * Real.log r) := by
  rw [complementary_cpow_lower_eq hN hr,
    mul_im]
  simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
  rw [show ((sigma : ℂ) + (gamma : ℂ) * I) - 1 =
      (((sigma - 1 : ℝ) : ℂ) + (gamma : ℂ) * I) by
        push_cast
        ring,
    ofReal_cpow_re_add_mul_I_im hr]
  ring

/-- Datum on a fixed vertical line in the critical strip. -/
def reflectedBiHeatVerticalDatum
    (P : ReflectedBiHeatDatum) (sigma gamma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    ReflectedBiHeatDatum where
  z := (sigma : ℂ) + (gamma : ℂ) * I
  x := P.x
  z_re_pos := by simpa using hsigma0
  z_re_lt_one := by simpa using hsigma1
  x_pos := P.x_pos

@[simp] theorem reflectedBiHeatVerticalDatum_z
    (P : ReflectedBiHeatDatum) (sigma gamma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1).z =
      (sigma : ℂ) + (gamma : ℂ) * I := rfl

@[simp] theorem reflectedBiHeatVerticalDatum_x
    (P : ReflectedBiHeatDatum) (sigma gamma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1).x = P.x := rfl

/-- Exact paired imaginary channel at height `gamma`. -/
def reflectedBiHeatFinitePartMixedPhaseAtom
    (sigma x gamma : ℝ) (p : ℕ × ℕ) : ℝ :=
  let d := (p.1 : ℝ) + 1
  let N := (p.2 : ℝ) + 1
  let r := (N + d) / N
  heatCoeff x ((p.1 : ℤ) + 1) * (1 / N) *
    (r ^ (sigma - 1) - r ^ (-sigma)) *
      Real.sin (gamma * Real.log r)

theorem reflectedBiHeatUpperSucc_add_lower_im_eq_mixedPhaseAtom
    (P : ReflectedBiHeatDatum) (sigma gamma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (p : ℕ × ℕ) :
    (reflectedBiHeatUpperRowTerm
          (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1) 0
          (p.1 + 1, p.2) +
        reflectedBiHeatLowerRowTerm
          (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1) 0 p).im =
      reflectedBiHeatFinitePartMixedPhaseAtom sigma P.x gamma p := by
  let d : ℝ := (p.1 : ℝ) + 1
  let N : ℝ := (p.2 : ℝ) + 1
  let r : ℝ := (N + d) / N
  have hN : 0 < N := by dsimp [N]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hNr : N * r = N + d := by
    dsimp [r]
    field_simp
  have hbaseUpper :
      (p.2 : ℂ) + ((p.1 : ℂ) + 1) + 1 = (((N * r : ℝ) : ℂ)) := by
    norm_cast
    rw [hNr]
    dsimp [N, d]
    push_cast
    ring
  have hbaseLower :
      (p.2 : ℂ) + (p.1 : ℂ) + 1 + 1 = (((N * r : ℝ) : ℂ)) := by
    norm_cast
    rw [hNr]
    dsimp [N, d]
    push_cast
    ring
  have hbaseN : (p.2 : ℂ) + 1 = (N : ℂ) := by
    norm_cast
    dsimp [N]
    push_cast
    ring
  rw [reflectedBiHeatUpperRowTerm, reflectedBiHeatLowerRowTerm,
    reflectedBiHeatFinitePartMixedPhaseAtom, reflectedBiHeatRowModel]
  simp only [ReflectedBiHeatDatum.leftOrder, ReflectedBiHeatDatum.rightOrder,
    reflectedBiHeatVerticalDatum_z, reflectedBiHeatVerticalDatum_x,
    zero_div, add_zero]
  push_cast
  rw [heatCoeff_neg]
  rw [hbaseUpper, hbaseLower, hbaseN]
  let U : ℂ := (((N * r : ℝ) : ℂ) ^
      (-((sigma : ℂ) + (gamma : ℂ) * I))) *
    (N : ℂ) ^ (-(1 - ((sigma : ℂ) + (gamma : ℂ) * I)))
  let L : ℂ := (N : ℂ) ^
      (-((sigma : ℂ) + (gamma : ℂ) * I)) *
    (((N * r : ℝ) : ℂ) ^
      (-(1 - ((sigma : ℂ) + (gamma : ℂ) * I))))
  change (((heatCoeff P.x ((p.1 : ℤ) + 1) : ℝ) : ℂ) *
        (U - (N : ℂ) ^ (-1)) +
      ((heatCoeff P.x ((p.1 : ℤ) + 1) : ℝ) : ℂ) *
        (L - (N : ℂ) ^ (-1))).im =
    heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) *
      (r ^ (sigma - 1) - r ^ (-sigma)) *
        Real.sin (gamma * Real.log r)
  have hU : U.im = -(1 / N * r ^ (-sigma) *
      Real.sin (gamma * Real.log r)) := by
    exact complementary_cpow_upper_im hN hr
  have hL : L.im = 1 / N * r ^ (sigma - 1) *
      Real.sin (gamma * Real.log r) := by
    exact complementary_cpow_lower_im hN hr
  simp only [add_im, mul_im, sub_im, ofReal_re, ofReal_im,
    zero_mul, add_zero, Complex.cpow_neg_one, inv_im, neg_zero]
  rw [hU, hL]
  ring

/-- Split an upper row into its zero-difference row and positive-difference rows. -/
def reflectedBiHeatUpperSuccSplitEquiv :
    (ℕ × ℕ) ⊕ ℕ ≃ ℕ × ℕ where
  toFun
    | Sum.inl p => (p.1 + 1, p.2)
    | Sum.inr n => (0, n)
  invFun
    | (0, n) => Sum.inr n
    | (k + 1, n) => Sum.inl (k, n)
  left_inv q := by
    rcases q with p | n
    · rcases p with ⟨k, n⟩
      rfl
    · rfl
  right_inv p := by rcases p with ⟨k, n⟩; cases k <;> rfl

@[simp] theorem reflectedBiHeatUpperSuccSplitEquiv_inl (p : ℕ × ℕ) :
    reflectedBiHeatUpperSuccSplitEquiv (Sum.inl p) = (p.1 + 1, p.2) := rfl

@[simp] theorem reflectedBiHeatUpperSuccSplitEquiv_inr (n : ℕ) :
    reflectedBiHeatUpperSuccSplitEquiv (Sum.inr n) = (0, n) := rfl

theorem reflectedBiHeatUpperRowTerm_zero_difference
    (P : ReflectedBiHeatDatum) (n : ℕ) :
    reflectedBiHeatUpperRowTerm P 0 (0, n) = 0 := by
  rw [reflectedBiHeatUpperRowTerm,
    reflectedBiHeatUpperRow_sub_model_eq]
  simp

theorem summable_reflectedBiHeatFinitePartMixedPhaseAtom
    (P : ReflectedBiHeatDatum) (sigma gamma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    Summable (reflectedBiHeatFinitePartMixedPhaseAtom sigma P.x gamma) := by
  let D := reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1
  have hreg : Summable (reflectedBiHeatRegularTerm D 0) :=
    summable_reflectedBiHeatRegularTerm_on_residueDisc D (by
      simp [D.residueRadius_pos.le])
  have hupper : Summable (fun p : ℕ × ℕ =>
      reflectedBiHeatUpperRowTerm D 0 p) := by
    refine (hreg.comp_injective (i := Sum.inl)
      (fun _ _ h => Sum.inl.inj h)).congr ?_
    intro p
    rfl
  have hlower : Summable (fun p : ℕ × ℕ =>
      reflectedBiHeatLowerRowTerm D 0 p) := by
    refine (hreg.comp_injective (i := Sum.inr)
      (fun _ _ h => Sum.inr.inj h)).congr ?_
    intro p
    rfl
  have hsuccMap : Function.Injective
      (fun p : ℕ × ℕ => (p.1 + 1, p.2)) := by
    intro a b h
    apply Prod.ext
    · exact Nat.add_right_cancel (congrArg Prod.fst h)
    · simpa using congrArg Prod.snd h
  have hupperSucc : Summable (fun p : ℕ × ℕ =>
      reflectedBiHeatUpperRowTerm D 0 (p.1 + 1, p.2)) := by
    refine (hupper.comp_injective hsuccMap).congr ?_
    intro p
    rfl
  have hpair := hupperSucc.add hlower
  have him : Summable (fun p : ℕ × ℕ =>
      (reflectedBiHeatUpperRowTerm D 0 (p.1 + 1, p.2) +
        reflectedBiHeatLowerRowTerm D 0 p).im) := by
    refine (hpair.map Complex.imCLM Complex.imCLM.continuous).congr ?_
    intro p
    simp [Complex.imCLM_apply]
  refine him.congr fun p => ?_
  exact reflectedBiHeatUpperSucc_add_lower_im_eq_mixedPhaseAtom
    P sigma gamma hsigma0 hsigma1 p

/-- Complete paired imaginary phase channel. -/
def reflectedBiHeatFinitePartMixedPhase
    (sigma gamma : ℝ) (P : ReflectedBiHeatDatum) : ℝ :=
  ∑' p : ℕ × ℕ,
    reflectedBiHeatFinitePartMixedPhaseAtom sigma P.x gamma p

theorem reflectedBiHeatFinitePart_vertical_im_eq_mixedPhase
    (P : ReflectedBiHeatDatum) (sigma gamma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    (reflectedBiHeatFinitePart
      (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1)).im =
      reflectedBiHeatFinitePartMixedPhase sigma gamma P := by
  let D := reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1
  let upper : ℕ × ℕ → ℂ := fun p =>
    reflectedBiHeatUpperRowTerm D 0 p
  let lower : ℕ × ℕ → ℂ := fun p =>
    reflectedBiHeatLowerRowTerm D 0 p
  let upperSucc : ℕ × ℕ → ℂ := fun p => upper (p.1 + 1, p.2)
  have hreg : Summable (reflectedBiHeatRegularTerm D 0) :=
    summable_reflectedBiHeatRegularTerm_on_residueDisc D (by
      simp [D.residueRadius_pos.le])
  have hupper : Summable upper := by
    refine (hreg.comp_injective (i := Sum.inl)
      (fun _ _ h => Sum.inl.inj h)).congr ?_
    intro p
    rfl
  have hlower : Summable lower := by
    refine (hreg.comp_injective (i := Sum.inr)
      (fun _ _ h => Sum.inr.inj h)).congr ?_
    intro p
    rfl
  have hsuccMap : Function.Injective
      (fun p : ℕ × ℕ => (p.1 + 1, p.2)) := by
    intro a b h
    apply Prod.ext
    · exact Nat.add_right_cancel (congrArg Prod.fst h)
    · simpa using congrArg Prod.snd h
  have hupperSucc : Summable upperSucc := by
    refine (hupper.comp_injective hsuccMap).congr ?_
    intro p
    rfl
  have hzero : HasSum (fun n : ℕ => upper (0, n)) 0 := by
    refine hasSum_zero.congr_fun fun n => ?_
    simpa [upper] using reflectedBiHeatUpperRowTerm_zero_difference D n
  have hsplitHas : HasSum
      (fun q : (ℕ × ℕ) ⊕ ℕ =>
        upper (reflectedBiHeatUpperSuccSplitEquiv q))
      ((∑' p, upperSucc p) + 0) := by
    exact HasSum.sum (f := fun q : (ℕ × ℕ) ⊕ ℕ =>
      upper (reflectedBiHeatUpperSuccSplitEquiv q))
      hupperSucc.hasSum hzero
  have hupperTsum : (∑' p, upper p) = ∑' p, upperSucc p := by
    calc
      (∑' p, upper p) = ∑' q : (ℕ × ℕ) ⊕ ℕ,
          upper (reflectedBiHeatUpperSuccSplitEquiv q) :=
        (reflectedBiHeatUpperSuccSplitEquiv.tsum_eq upper).symm
      _ = (∑' p, upperSucc p) + 0 := hsplitHas.tsum_eq
      _ = ∑' p, upperSucc p := add_zero _
  have hregularSplit : reflectedBiHeatRegularSum D 0 =
      (∑' p, upper p) + ∑' p, lower p := by
    rw [reflectedBiHeatRegularSum]
    exact (HasSum.sum (f := reflectedBiHeatRegularTerm D 0)
      hupper.hasSum hlower.hasSum).tsum_eq
  let pair : ℕ × ℕ → ℂ := fun p => upperSucc p + lower p
  have hpair : Summable pair := by
    exact hupperSucc.add hlower
  have hregularPair : reflectedBiHeatRegularSum D 0 =
      (∑' p : ℕ × ℕ, pair p) := by
    rw [hregularSplit, hupperTsum, hupperSucc.tsum_add hlower]
  rw [show reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1 = D by rfl,
    reflectedBiHeatFinitePart, hregularPair]
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  rw [Complex.im_tsum hpair, reflectedBiHeatFinitePartMixedPhase]
  simp only [mul_zero, zero_add]
  apply tsum_congr
  intro p
  change (upperSucc p + lower p).im = _
  exact reflectedBiHeatUpperSucc_add_lower_im_eq_mixedPhaseAtom
    P sigma gamma hsigma0 hsigma1 p

/-- Paired upper/lower neutral-height slope atom. -/
def reflectedBiHeatFinitePartMixedSlopeAtom
    (sigma x : ℝ) (p : ℕ × ℕ) : ℝ :=
  let d := (p.1 : ℝ) + 1
  let N := (p.2 : ℝ) + 1
  let r := (N + d) / N
  heatCoeff x ((p.1 : ℤ) + 1) * (1 / N) *
    (r ^ (sigma - 1) - r ^ (-sigma)) * Real.log r

/-- Summable Gaussian/inverse-square bound for paired slope atoms. -/
def reflectedBiHeatFinitePartMixedSlopeMajorant
    (P : ReflectedBiHeatDatum) (p : ℕ × ℕ) : ℝ :=
  2 * (((p.1 : ℝ) + 1) *
    (heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / (((p.2 : ℝ) + 1) ^ 2))))

theorem summable_reflectedBiHeatFinitePartMixedSlopeMajorant
    (P : ReflectedBiHeatDatum) :
    Summable (reflectedBiHeatFinitePartMixedSlopeMajorant P) := by
  have hd : Summable (fun k : ℕ =>
      ((k : ℝ) + 1) * heatCoeff P.x ((k : ℤ) + 1)) := by
    refine (summable_nat_add_one_mul_heatCoeff P).congr fun k => ?_
    rw [heatCoeff_neg]
  have hn : Summable (fun n : ℕ =>
      1 / (((n : ℝ) + 1) ^ 2)) :=
    GaloisForLFunctions.RHTower.summable_inv_succ_sq
  have hproduct := hd.mul_of_nonneg hn
    (fun k => mul_nonneg (by positivity) (heatCoeff_pos P.x _).le)
    (fun n => by positivity)
  refine hproduct.mul_left 2 |>.congr fun p => ?_
  rw [reflectedBiHeatFinitePartMixedSlopeMajorant]
  ring

theorem abs_reflectedBiHeatFinitePartMixedSlopeAtom_le
    (P : ReflectedBiHeatDatum) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (p : ℕ × ℕ) :
    |reflectedBiHeatFinitePartMixedSlopeAtom sigma P.x p| ≤
      reflectedBiHeatFinitePartMixedSlopeMajorant P p := by
  let d : ℝ := (p.1 : ℝ) + 1
  let N : ℝ := (p.2 : ℝ) + 1
  let r : ℝ := (N + d) / N
  have hd : 0 < d := by dsimp [d]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hr : 1 < r := by
    dsimp [r]
    rw [lt_div_iff₀ hN]
    linarith
  have hrle : 1 ≤ r := hr.le
  have hpowLeft : r ^ (sigma - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrle (by linarith)
  have hpowRight : r ^ (-sigma) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrle (by linarith)
  have hr0 : 0 ≤ r := (lt_trans zero_lt_one hr).le
  have hpowLeft0 : 0 ≤ r ^ (sigma - 1) := Real.rpow_nonneg hr0 _
  have hpowRight0 : 0 ≤ r ^ (-sigma) := Real.rpow_nonneg hr0 _
  have hdiff : |r ^ (sigma - 1) - r ^ (-sigma)| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hrle
  have hlog : Real.log r ≤ d / N := by
    calc
      Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hr)
      _ = d / N := by
        dsimp [r]
        field_simp
        ring
  rw [reflectedBiHeatFinitePartMixedSlopeAtom,
    reflectedBiHeatFinitePartMixedSlopeMajorant]
  change |heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) *
      (r ^ (sigma - 1) - r ^ (-sigma)) * Real.log r| ≤
    2 * (d * (heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N ^ 2)))
  rw [abs_mul, abs_mul, abs_mul,
    abs_of_pos (heatCoeff_pos P.x _), abs_of_pos (one_div_pos.mpr hN),
    abs_of_nonneg hlog0]
  have hfront0 : 0 ≤ heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) :=
    mul_nonneg (heatCoeff_pos P.x _).le (one_div_pos.mpr hN).le
  calc
    heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) *
          |r ^ (sigma - 1) - r ^ (-sigma)| * Real.log r ≤
        heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) * 2 * Real.log r := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiff hfront0) hlog0
    _ ≤ heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N) * 2 * (d / N) := by
      exact mul_le_mul_of_nonneg_left hlog (mul_nonneg hfront0 (by norm_num))
    _ = 2 * (d * (heatCoeff P.x ((p.1 : ℤ) + 1) * (1 / N ^ 2))) := by
      field_simp

theorem summable_reflectedBiHeatFinitePartMixedSlopeAtom
    (P : ReflectedBiHeatDatum) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    Summable (reflectedBiHeatFinitePartMixedSlopeAtom sigma P.x) := by
  apply Summable.of_norm_bounded
    (summable_reflectedBiHeatFinitePartMixedSlopeMajorant P)
  intro p
  rw [Real.norm_eq_abs]
  exact abs_reflectedBiHeatFinitePartMixedSlopeAtom_le P hsigma0 hsigma1 p

theorem reflectedBiHeatFinitePartMixedSlopeAtom_pos_of_half_lt
    {sigma x : ℝ} (hsigma : 1 / 2 < sigma) (p : ℕ × ℕ) :
    0 < reflectedBiHeatFinitePartMixedSlopeAtom sigma x p := by
  let d : ℝ := (p.1 : ℝ) + 1
  let N : ℝ := (p.2 : ℝ) + 1
  let r : ℝ := (N + d) / N
  have hN : 0 < N := by dsimp [N]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 1 < r := by
    dsimp [r]
    rw [lt_div_iff₀ hN]
    linarith
  have hpows : r ^ (-sigma) < r ^ (sigma - 1) :=
    (Real.strictMono_rpow_of_base_gt_one hr) (by linarith)
  rw [reflectedBiHeatFinitePartMixedSlopeAtom]
  change 0 < heatCoeff x ((p.1 : ℤ) + 1) * (1 / N) *
    (r ^ (sigma - 1) - r ^ (-sigma)) * Real.log r
  exact mul_pos (mul_pos (mul_pos (heatCoeff_pos x _) (one_div_pos.mpr hN))
    (sub_pos.mpr hpows)) (Real.log_pos hr)

theorem reflectedBiHeatFinitePartMixedSlopeAtom_neg_of_lt_half
    {sigma x : ℝ} (hsigma : sigma < 1 / 2) (p : ℕ × ℕ) :
    reflectedBiHeatFinitePartMixedSlopeAtom sigma x p < 0 := by
  let d : ℝ := (p.1 : ℝ) + 1
  let N : ℝ := (p.2 : ℝ) + 1
  let r : ℝ := (N + d) / N
  have hN : 0 < N := by dsimp [N]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 1 < r := by
    dsimp [r]
    rw [lt_div_iff₀ hN]
    linarith
  have hpows : r ^ (sigma - 1) < r ^ (-sigma) :=
    (Real.strictMono_rpow_of_base_gt_one hr) (by linarith)
  rw [reflectedBiHeatFinitePartMixedSlopeAtom]
  change heatCoeff x ((p.1 : ℤ) + 1) * (1 / N) *
    (r ^ (sigma - 1) - r ^ (-sigma)) * Real.log r < 0
  have hfront : 0 < heatCoeff x ((p.1 : ℤ) + 1) * (1 / N) * Real.log r :=
    mul_pos (mul_pos (heatCoeff_pos x _) (one_div_pos.mpr hN)) (Real.log_pos hr)
  rw [show heatCoeff x ((p.1 : ℤ) + 1) * (1 / N) *
      (r ^ (sigma - 1) - r ^ (-sigma)) * Real.log r =
    (heatCoeff x ((p.1 : ℤ) + 1) * (1 / N) * Real.log r) *
      (r ^ (sigma - 1) - r ^ (-sigma)) by ring]
  exact mul_neg_of_pos_of_neg hfront (sub_neg.mpr hpows)

/-- Complete paired neutral-height slope series. -/
def reflectedBiHeatFinitePartMixedSlope
    (sigma : ℝ) (P : ReflectedBiHeatDatum) : ℝ :=
  ∑' p : ℕ × ℕ, reflectedBiHeatFinitePartMixedSlopeAtom sigma P.x p

theorem reflectedBiHeatFinitePartMixedSlope_pos_of_half_lt
    (P : ReflectedBiHeatDatum) {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    0 < reflectedBiHeatFinitePartMixedSlope sigma P := by
  have hs := summable_reflectedBiHeatFinitePartMixedSlopeAtom P
    (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hsigma) hsigma1
  exact hs.tsum_pos
    (fun p => (reflectedBiHeatFinitePartMixedSlopeAtom_pos_of_half_lt hsigma p).le)
    (0, 0) (reflectedBiHeatFinitePartMixedSlopeAtom_pos_of_half_lt hsigma (0, 0))

theorem reflectedBiHeatFinitePartMixedSlope_neg_of_lt_half
    (P : ReflectedBiHeatDatum) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma : sigma < 1 / 2) :
    reflectedBiHeatFinitePartMixedSlope sigma P < 0 := by
  have hs := summable_reflectedBiHeatFinitePartMixedSlopeAtom P hsigma0
    (lt_trans hsigma (by norm_num : (1 / 2 : ℝ) < 1))
  have hsneg : Summable (fun p : ℕ × ℕ =>
      -reflectedBiHeatFinitePartMixedSlopeAtom sigma P.x p) := hs.neg
  have hpos : 0 < ∑' p : ℕ × ℕ,
      -reflectedBiHeatFinitePartMixedSlopeAtom sigma P.x p :=
    hsneg.tsum_pos
      (fun p => (neg_pos.mpr
        (reflectedBiHeatFinitePartMixedSlopeAtom_neg_of_lt_half hsigma p)).le)
      (0, 0) (neg_pos.mpr
        (reflectedBiHeatFinitePartMixedSlopeAtom_neg_of_lt_half hsigma (0, 0)))
  rw [tsum_neg] at hpos
  exact neg_pos.mp hpos

theorem reflectedBiHeatFinitePartMixedSlope_half (P : ReflectedBiHeatDatum) :
    reflectedBiHeatFinitePartMixedSlope (1 / 2) P = 0 := by
  rw [reflectedBiHeatFinitePartMixedSlope]
  calc
    (∑' p : ℕ × ℕ,
        reflectedBiHeatFinitePartMixedSlopeAtom (1 / 2) P.x p) =
        ∑' _p : ℕ × ℕ, (0 : ℝ) := tsum_congr (fun p => by
          rw [reflectedBiHeatFinitePartMixedSlopeAtom]
          norm_num)
    _ = 0 := tsum_zero

theorem reflectedBiHeatFinitePartMixedSlope_eq_zero_iff
    (P : ReflectedBiHeatDatum) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    reflectedBiHeatFinitePartMixedSlope sigma P = 0 ↔ sigma = 1 / 2 := by
  constructor
  · intro h
    rcases lt_trichotomy sigma (1 / 2) with hlt | heq | hgt
    · linarith [reflectedBiHeatFinitePartMixedSlope_neg_of_lt_half P hsigma0 hlt]
    · exact heq
    · linarith [reflectedBiHeatFinitePartMixedSlope_pos_of_half_lt P hgt hsigma1]
  · rintro rfl
    exact reflectedBiHeatFinitePartMixedSlope_half P

/-- Height derivative of one paired imaginary-phase atom. -/
def reflectedBiHeatFinitePartMixedPhaseDerivativeAtom
    (sigma x gamma : ℝ) (p : ℕ × ℕ) : ℝ :=
  let N := (p.2 : ℝ) + 1
  let d := (p.1 : ℝ) + 1
  let r := (N + d) / N
  reflectedBiHeatFinitePartMixedSlopeAtom sigma x p *
    Real.cos (gamma * Real.log r)

theorem hasDerivAt_reflectedBiHeatFinitePartMixedPhaseAtom
    (sigma x gamma : ℝ) (p : ℕ × ℕ) :
    HasDerivAt
      (fun t => reflectedBiHeatFinitePartMixedPhaseAtom sigma x t p)
      (reflectedBiHeatFinitePartMixedPhaseDerivativeAtom sigma x gamma p)
      gamma := by
  let N : ℝ := (p.2 : ℝ) + 1
  let d : ℝ := (p.1 : ℝ) + 1
  let r : ℝ := (N + d) / N
  let c : ℝ := heatCoeff x ((p.1 : ℤ) + 1) * (1 / N) *
    (r ^ (sigma - 1) - r ^ (-sigma))
  have hlin : HasDerivAt (fun t : ℝ => t * Real.log r)
      (Real.log r) gamma := by
    simpa using (hasDerivAt_id gamma).mul_const (Real.log r)
  have h := hlin.sin.const_mul c
  change HasDerivAt (fun t => c * Real.sin (t * Real.log r))
    ((c * Real.log r) * Real.cos (gamma * Real.log r)) gamma
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem norm_reflectedBiHeatFinitePartMixedPhaseDerivativeAtom_le
    (P : ReflectedBiHeatDatum) {sigma : ℝ}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (gamma : ℝ) (p : ℕ × ℕ) :
    ‖reflectedBiHeatFinitePartMixedPhaseDerivativeAtom
        sigma P.x gamma p‖ ≤
      reflectedBiHeatFinitePartMixedSlopeMajorant P p := by
  rw [reflectedBiHeatFinitePartMixedPhaseDerivativeAtom,
    Real.norm_eq_abs, abs_mul]
  calc
    |reflectedBiHeatFinitePartMixedSlopeAtom sigma P.x p| *
          |Real.cos (gamma * Real.log
            (((p.2 : ℝ) + 1 + ((p.1 : ℝ) + 1)) /
              ((p.2 : ℝ) + 1)))| ≤
        |reflectedBiHeatFinitePartMixedSlopeAtom sigma P.x p| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
        (abs_nonneg _)
    _ = |reflectedBiHeatFinitePartMixedSlopeAtom sigma P.x p| := mul_one _
    _ ≤ reflectedBiHeatFinitePartMixedSlopeMajorant P p :=
      abs_reflectedBiHeatFinitePartMixedSlopeAtom_le
        P hsigma0 hsigma1 p

theorem hasDerivAt_reflectedBiHeatFinitePartMixedPhase
    (P : ReflectedBiHeatDatum) (sigma gamma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    HasDerivAt
      (fun t => reflectedBiHeatFinitePartMixedPhase sigma t P)
      (∑' p : ℕ × ℕ,
        reflectedBiHeatFinitePartMixedPhaseDerivativeAtom
          sigma P.x gamma p)
      gamma := by
  change HasDerivAt
    (fun t => ∑' p : ℕ × ℕ,
      reflectedBiHeatFinitePartMixedPhaseAtom sigma P.x t p)
    (∑' p : ℕ × ℕ,
      reflectedBiHeatFinitePartMixedPhaseDerivativeAtom sigma P.x gamma p)
    gamma
  apply hasDerivAt_tsum_of_isPreconnected
    (u := reflectedBiHeatFinitePartMixedSlopeMajorant P)
    (g := fun p t =>
      reflectedBiHeatFinitePartMixedPhaseAtom sigma P.x t p)
    (g' := fun p t =>
      reflectedBiHeatFinitePartMixedPhaseDerivativeAtom sigma P.x t p)
    (t := Set.univ) (y₀ := 0) (y := gamma)
  · exact summable_reflectedBiHeatFinitePartMixedSlopeMajorant P
  · exact isOpen_univ
  · exact isPreconnected_univ
  · intro p y _
    exact hasDerivAt_reflectedBiHeatFinitePartMixedPhaseAtom sigma P.x y p
  · intro p y _
    exact norm_reflectedBiHeatFinitePartMixedPhaseDerivativeAtom_le
      P hsigma0 hsigma1 y p
  · trivial
  · refine summable_zero.congr fun p => ?_
    rw [reflectedBiHeatFinitePartMixedPhaseAtom]
    simp
  · trivial

theorem hasDerivAt_reflectedBiHeatFinitePartMixedPhase_zero
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    HasDerivAt
      (fun gamma => reflectedBiHeatFinitePartMixedPhase sigma gamma P)
      (reflectedBiHeatFinitePartMixedSlope sigma P) 0 := by
  have h := hasDerivAt_reflectedBiHeatFinitePartMixedPhase
    P sigma 0 hsigma0 hsigma1
  convert h using 1
  rw [reflectedBiHeatFinitePartMixedSlope]
  apply tsum_congr
  intro p
  rw [reflectedBiHeatFinitePartMixedPhaseDerivativeAtom]
  simp

/-- The canonical finite-part imaginary channel has the strict signed slope
`sign (sigma - 1/2)` at neutral height. -/
theorem hasDerivAt_reflectedBiHeatFinitePart_vertical_im_zero
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    HasDerivAt
      (fun gamma => (reflectedBiHeatFinitePart
        (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1)).im)
      (reflectedBiHeatFinitePartMixedSlope sigma P) 0 := by
  have heq : (fun gamma => (reflectedBiHeatFinitePart
      (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1)).im) =
      fun gamma => reflectedBiHeatFinitePartMixedPhase sigma gamma P := by
    funext gamma
    exact reflectedBiHeatFinitePart_vertical_im_eq_mixedPhase
      P sigma gamma hsigma0 hsigma1
  rw [heq]
  exact hasDerivAt_reflectedBiHeatFinitePartMixedPhase_zero
    P sigma hsigma0 hsigma1

theorem eventually_reflectedBiHeatFinitePart_vertical_im_ne_zero
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hoffWall : sigma ≠ 1 / 2) :
    ∀ᶠ gamma : ℝ in 𝓝[≠] 0,
      (reflectedBiHeatFinitePart
        (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1)).im ≠ 0 := by
  have hslope : reflectedBiHeatFinitePartMixedSlope sigma P ≠ 0 :=
    fun h => hoffWall
      ((reflectedBiHeatFinitePartMixedSlope_eq_zero_iff
        P hsigma0 hsigma1).1 h)
  exact (hasDerivAt_reflectedBiHeatFinitePart_vertical_im_zero
    P sigma hsigma0 hsigma1).eventually_ne hslope

theorem reflectedBiHeatFinitePartMixedPhase_zero
    (P : ReflectedBiHeatDatum) (sigma : ℝ) :
    reflectedBiHeatFinitePartMixedPhase sigma 0 P = 0 := by
  rw [reflectedBiHeatFinitePartMixedPhase]
  calc
    (∑' p : ℕ × ℕ,
        reflectedBiHeatFinitePartMixedPhaseAtom sigma P.x 0 p) =
        ∑' _p : ℕ × ℕ, (0 : ℝ) := tsum_congr (fun p => by
          rw [reflectedBiHeatFinitePartMixedPhaseAtom]
          simp)
    _ = 0 := tsum_zero

theorem reflectedBiHeatFinitePart_vertical_im_zero
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    (reflectedBiHeatFinitePart
      (reflectedBiHeatVerticalDatum P sigma 0 hsigma0 hsigma1)).im = 0 := by
  rw [reflectedBiHeatFinitePart_vertical_im_eq_mixedPhase]
  exact reflectedBiHeatFinitePartMixedPhase_zero P sigma

theorem eventually_reflectedBiHeatFinitePart_vertical_im_div_pos_of_half_lt
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    ∀ᶠ gamma : ℝ in 𝓝[≠] 0,
      0 < (reflectedBiHeatFinitePart
        (reflectedBiHeatVerticalDatum P sigma gamma
          (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hsigma) hsigma1)).im /
          gamma := by
  let hsigma0 : 0 < sigma :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hsigma
  let f : ℝ → ℝ := fun gamma => (reflectedBiHeatFinitePart
    (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1)).im
  have hf : HasDerivAt f
      (reflectedBiHeatFinitePartMixedSlope sigma P) 0 :=
    hasDerivAt_reflectedBiHeatFinitePart_vertical_im_zero
      P sigma hsigma0 hsigma1
  have hf0 : f 0 = 0 :=
    reflectedBiHeatFinitePart_vertical_im_zero P sigma hsigma0 hsigma1
  have hpos : 0 < reflectedBiHeatFinitePartMixedSlope sigma P :=
    reflectedBiHeatFinitePartMixedSlope_pos_of_half_lt P hsigma hsigma1
  have hslope : Tendsto (slope f 0) (𝓝[≠] (0 : ℝ))
      (𝓝 (reflectedBiHeatFinitePartMixedSlope sigma P)) :=
    hasDerivAt_iff_tendsto_slope.1 hf
  have hevent := hslope.eventually (eventually_gt_nhds hpos)
  refine hevent.mono fun gamma hgamma => ?_
  rw [slope_def_field, hf0, sub_zero, sub_zero, div_eq_inv_mul] at hgamma
  simpa [f, hsigma0, div_eq_inv_mul] using hgamma

theorem eventually_reflectedBiHeatFinitePart_vertical_im_div_neg_of_lt_half
    (P : ReflectedBiHeatDatum) (sigma : ℝ)
    (hsigma0 : 0 < sigma) (hsigma : sigma < 1 / 2) :
    ∀ᶠ gamma : ℝ in 𝓝[≠] 0,
      (reflectedBiHeatFinitePart
        (reflectedBiHeatVerticalDatum P sigma gamma hsigma0
          (lt_trans hsigma (by norm_num : (1 / 2 : ℝ) < 1)))).im /
          gamma < 0 := by
  let hsigma1 : sigma < 1 :=
    lt_trans hsigma (by norm_num : (1 / 2 : ℝ) < 1)
  let f : ℝ → ℝ := fun gamma => (reflectedBiHeatFinitePart
    (reflectedBiHeatVerticalDatum P sigma gamma hsigma0 hsigma1)).im
  have hf : HasDerivAt f
      (reflectedBiHeatFinitePartMixedSlope sigma P) 0 :=
    hasDerivAt_reflectedBiHeatFinitePart_vertical_im_zero
      P sigma hsigma0 hsigma1
  have hf0 : f 0 = 0 :=
    reflectedBiHeatFinitePart_vertical_im_zero P sigma hsigma0 hsigma1
  have hneg : reflectedBiHeatFinitePartMixedSlope sigma P < 0 :=
    reflectedBiHeatFinitePartMixedSlope_neg_of_lt_half P hsigma0 hsigma
  have hslope : Tendsto (slope f 0) (𝓝[≠] (0 : ℝ))
      (𝓝 (reflectedBiHeatFinitePartMixedSlope sigma P)) :=
    hasDerivAt_iff_tendsto_slope.1 hf
  have hevent := hslope.eventually (eventually_lt_nhds hneg)
  refine hevent.mono fun gamma hgamma => ?_
  rw [slope_def_field, hf0, sub_zero, sub_zero, div_eq_inv_mul] at hgamma
  simpa [f, hsigma1, div_eq_inv_mul] using hgamma

end RHTower
