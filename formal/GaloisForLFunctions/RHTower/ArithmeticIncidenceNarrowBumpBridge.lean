import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional

/-!
# Full-Weil calibration on the odd integer-log lattice

Exact subtraction of the common single-packet energy cancels the singular
archimedean diagonal. Integer-log separation selects every prime resonance
simultaneously, while an explicit bound controls the remaining signed pole and
Gamma interactions uniformly over all coefficient vectors.
-/

open MeasureTheory Set Filter Topology Zeta23
open RHTower.WeilOneSided RHTower.ArchimedeanAnomaly
open RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty
open scoped ContDiff

noncomputable section

namespace RHTower.ArithmeticIncidenceBump

/-- The positive and negative copies of the integer labels `2, ..., N+1`. -/
abbrev LatticeIndex (N : ℕ) := Fin N × Bool

def label {N : ℕ} (i : LatticeIndex N) : ℕ := i.1.val + 2

def numerator {N : ℕ} (i : LatticeIndex N) : ℕ := if i.2 then label i else 1

def denominator {N : ℕ} (i : LatticeIndex N) : ℕ := if i.2 then 1 else label i

/-- Signed logarithmic centre in rational normal form. -/
def position {N : ℕ} (i : LatticeIndex N) : ℝ :=
  Real.log (numerator i) - Real.log (denominator i)

def amplitude {N : ℕ} (c : Fin N → ℝ) (i : LatticeIndex N) : ℝ :=
  if i.2 then c i.1 else -c i.1

theorem label_two_le {N : ℕ} (i : LatticeIndex N) : 2 ≤ label i := by
  unfold label; omega

theorem label_le {N : ℕ} (i : LatticeIndex N) : label i ≤ N + 2 := by
  have hi := i.1.isLt
  unfold label; omega

theorem numerator_bounds {N : ℕ} (i : LatticeIndex N) :
    1 ≤ numerator i ∧ numerator i ≤ N + 2 := by
  have h₁ := label_two_le i
  have h₂ := label_le i
  unfold numerator
  split <;> omega

theorem denominator_bounds {N : ℕ} (i : LatticeIndex N) :
    1 ≤ denominator i ∧ denominator i ≤ N + 2 := by
  have h₁ := label_two_le i
  have h₂ := label_le i
  unfold denominator
  split <;> omega

theorem position_eq {N : ℕ} (i : LatticeIndex N) :
    position i = if i.2 then Real.log (label i) else -Real.log (label i) := by
  unfold position numerator denominator
  split <;> simp only [Nat.cast_one, Real.log_one, sub_zero, zero_sub]

theorem log_label_pos {N : ℕ} (i : LatticeIndex N) : 0 < Real.log (label i) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < label i from lt_of_lt_of_le (by omega) (label_two_le i))

theorem position_injective (N : ℕ) : Function.Injective (position (N := N)) := by
  rintro ⟨i, b⟩ ⟨k, d⟩ h
  have hi := log_label_pos (i, b)
  have hk := log_label_pos (k, d)
  have hpos (v : LatticeIndex N) : (0 : ℝ) < label v := by
    have hv := label_two_le v
    exact_mod_cast (show 0 < label v by omega)
  rw [position_eq, position_eq] at h
  cases b <;> cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · have he : Real.log (label (i, false)) = Real.log (label (k, false)) := neg_injective h
    have hn := Real.log_injOn_pos
      (hpos (i, false)) (hpos (k, false)) he
    have hn' : label (i, false) = label (k, false) := by exact_mod_cast hn
    have hik : i = k := Fin.ext (by simpa only [label, Nat.add_right_cancel_iff] using hn')
    subst k; rfl
  · exfalso; linarith
  · exfalso; linarith
  · have hn := Real.log_injOn_pos
      (hpos (i, true)) (hpos (k, true)) h
    have hn' : label (i, true) = label (k, true) := by exact_mod_cast hn
    have hik : i = k := Fin.ext (by simpa only [label, Nat.add_right_cancel_iff] using hn')
    subst k; rfl

private theorem log_nat_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Real.log (a * b : ℕ) = Real.log a + Real.log b := by
  rw [Nat.cast_mul, Real.log_mul]
  · exact_mod_cast (show a ≠ 0 by omega)
  · exact_mod_cast (show b ≠ 0 by omega)

/-- Every mismatch has a bounded integer denominator, even when the sampled integer is large. -/
theorem lag_identity {N n : ℕ} (hn : 1 ≤ n) (i k : LatticeIndex N) :
    Real.log n - position i + position k =
      Real.log (n * denominator i * numerator k : ℕ) -
        Real.log (numerator i * denominator k : ℕ) := by
  rw [log_nat_mul (Nat.mul_le_mul hn (denominator_bounds i).1) (numerator_bounds k).1,
    log_nat_mul hn (denominator_bounds i).1,
    log_nat_mul (numerator_bounds i).1 (denominator_bounds k).1]
  unfold position
  ring

/-- One separation bound controls every nonresonant prime sample on the complete lattice. -/
theorem lag_gap {N n : ℕ} (hn : 1 ≤ n) (i k : LatticeIndex N)
    (hne : position i - position k ≠ Real.log n) :
    1 / (((N + 2 : ℕ) : ℝ) ^ 2 + 1) ≤ |Real.log n - position i + position k| := by
  have hx : 1 ≤ n * denominator i * numerator k :=
    Nat.mul_le_mul (Nat.mul_le_mul hn (denominator_bounds i).1) (numerator_bounds k).1
  have hy : 1 ≤ numerator i * denominator k :=
    Nat.mul_le_mul (numerator_bounds i).1 (denominator_bounds k).1
  have hne' : n * denominator i * numerator k ≠ numerator i * denominator k := by
    intro he
    have hh := lag_identity hn i k
    rw [he, sub_self] at hh
    exact hne (by linarith)
  have hg := WeilExcess.inv_succ_le_abs_log_sub hx hy hne'
  rw [← lag_identity hn i k] at hg
  have hprod : numerator i * denominator k ≤ (N + 2) ^ 2 := by
    simpa only [sq] using Nat.mul_le_mul (numerator_bounds i).2 (denominator_bounds k).2
  have hden : (numerator i * denominator k : ℕ) + (1 : ℝ) ≤
      ((N + 2 : ℕ) : ℝ) ^ 2 + 1 := by exact_mod_cast Nat.add_le_add_right hprod 1
  exact (one_div_le_one_div_of_le (by positivity) hden).trans hg

/-- Distinct signed lattice centres have the same size-controlled separation. -/
theorem position_gap {N : ℕ} (i k : LatticeIndex N) (hik : i ≠ k) :
    1 / (((N + 2 : ℕ) : ℝ) ^ 2 + 1) ≤ |position i - position k| := by
  have hg := lag_gap (n := 1) (by omega) i k (by
    simp only [Nat.cast_one, Real.log_one]
    exact sub_ne_zero.mpr (fun h => hik (position_injective N h)))
  simpa only [Nat.cast_one, Real.log_one, zero_sub, neg_add_eq_sub, abs_sub_comm] using hg

theorem abs_position_le {N : ℕ} (i : LatticeIndex N) :
    |position i| ≤ Real.log (N + 2 : ℕ) := by
  have hp := log_label_pos i
  have ht := label_two_le i
  have hl := Real.log_le_log
    (show (0 : ℝ) < label i by exact_mod_cast (show 0 < label i by omega))
    (show (label i : ℝ) ≤ (N + 2 : ℕ) by exact_mod_cast label_le i)
  rw [position_eq]
  split <;> simpa only [abs_neg, abs_of_pos hp] using hl

/-- The pole channel sees only the logarithmic diameter of the integer lattice. -/
theorem position_span {N : ℕ} (i k : LatticeIndex N) :
    |position i - position k| ≤ 2 * Real.log (N + 2 : ℕ) :=
  (abs_sub _ _).trans (by linarith [abs_position_le i, abs_position_le k])

/-- Correlation radius of the canonical smooth bump. -/
def radius (j : ℕ) : ℝ := 1 / (2 * ((j : ℝ) + 1))

/-- Squared mass used to normalize all arithmetic samples. -/
def mass (j : ℕ) : ℝ := ∫ u, (narrowBump j u) ^ 2

theorem radius_pos (j : ℕ) : 0 < radius j := by unfold radius; positivity

theorem mass_pos (j : ℕ) : 0 < mass j := integral_narrowBump_sq_pos j

theorem bump_autocorr_zero (j : ℕ) : autocorr (narrowBump j) 0 = mass j := by
  simp only [autocorr, mass, add_zero, sq]

theorem bump_autocorr_vanish (j : ℕ) {t : ℝ} (ht : radius j < |t|) :
    autocorr (narrowBump j) t = 0 := by
  have h := weilTest_narrowBumpC_eq_zero j (Y := -t) (by simpa only [radius, abs_neg] using ht)
  unfold narrowBumpC at h
  rw [← autocorr_eq_weilTest] at h
  exact Complex.ofReal_eq_zero.mp h

theorem bump_autocorr_bound (j : ℕ) (t : ℝ) :
    |autocorr (narrowBump j) t| ≤ mass j := by
  rw [← bump_autocorr_zero]
  exact abs_autocorr_le_zero (narrowBump j).hasCompactSupport (narrowBump j).continuous t

/-- The absolute correlation mass is at most its support length times its diagonal mass. -/
theorem integral_abs_bump_autocorr_le (j : ℕ) :
    (∫ t, |autocorr (narrowBump j) t|) ≤ 2 * radius j * mass j := by
  have hs : ∀ t, t ∉ Icc (-radius j) (radius j) →
      |autocorr (narrowBump j) t| = 0 := by
    intro t ht
    have hfar : radius j < |t| := by
      by_contra h
      exact ht (abs_le.mp (le_of_not_gt h))
    rw [bump_autocorr_vanish j hfar, abs_zero]
  have hb := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Icc (-radius j) (radius j))
    (f := fun t => |autocorr (narrowBump j) t|)
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (fun t _ => by simpa only [Real.norm_eq_abs, abs_abs] using bump_autocorr_bound j t)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs] at hb
  have hnonneg : 0 ≤ ∫ t, |autocorr (narrowBump j) t| :=
    integral_nonneg fun t => abs_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [radius_pos j])] at hb
  nlinarith [hb]

/-- A finite real train, with no restriction on the signs of its coefficients. -/
def train {ι : Type*} (S : Finset ι) (c x : ι → ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ S, c i * narrowBump j (u - x i)

theorem contDiff_train {ι : Type*} (S : Finset ι) (c x : ι → ℝ) (j : ℕ) :
    ContDiff ℝ ∞ (train S c x j) := by
  exact ContDiff.sum fun i _ => contDiff_const.mul
    ((narrowBump j).contDiff.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_train {ι : Type*} (S : Finset ι) (c x : ι → ℝ) (j : ℕ) :
    HasCompactSupport (train S c x j) := by
  have h := HasCompactSupport.finset_sum (s := S)
    (f := fun i u => c i * narrowBump j (u - x i))
    (fun i _ => ((narrowBump j).hasCompactSupport.comp_homeomorph
      (Homeomorph.subRight (x i))).mul_left)
  have he : (∑ i ∈ S, fun u => c i * narrowBump j (u - x i)) = train S c x j := by
    funext u
    simp only [Finset.sum_apply, train]
  rwa [he] at h

/-- Each ordered pair contributes the correlation at its centre difference. -/
theorem autocorr_train {ι : Type*} (S : Finset ι) (c x : ι → ℝ) (j : ℕ) (t : ℝ) :
    autocorr (train S c x j) t =
      ∑ i ∈ S, ∑ k ∈ S, c i * c k * autocorr (narrowBump j) (t + x i - x k) := by
  have h := integral_translateComb_autocorr S c x
    (narrowBump j).continuous (narrowBump j).hasCompactSupport (-t)
  have he : ∀ (i k : ι) (u : ℝ), u - (-t + x k - x i) = u + (t + x i - x k) :=
    fun i k u => by ring
  simp_rw [he] at h
  simpa only [autocorr, train, sub_neg_eq_add] using h

/-- Correlation remaining after all same-centre terms are removed. -/
def offCorrelation {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c x : ι → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ S, ∑ k ∈ S,
    if i = k then 0 else c i * c k * autocorr (narrowBump j) (t + x i - x k)

/-- Exact diagonal removal, before any limit or estimate. -/
theorem autocorr_train_split {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c x : ι → ℝ) (j : ℕ) (t : ℝ) :
    autocorr (train S c x j) t =
      (∑ i ∈ S, c i ^ 2) * autocorr (narrowBump j) t + offCorrelation S c x j t := by
  have he (i k : ι) :
      c i * c k * autocorr (narrowBump j) (t + x i - x k) =
        (if k = i then c i ^ 2 * autocorr (narrowBump j) t else 0) +
        (if i = k then 0 else c i * c k * autocorr (narrowBump j) (t + x i - x k)) := by
    by_cases h : i = k
    · subst k; simp only [if_true, add_sub_cancel_right, add_zero, sq]
    · simp only [if_neg h, if_neg (Ne.symm h), zero_add]
  rw [autocorr_train]
  calc
    _ = ∑ i ∈ S, (c i ^ 2 * autocorr (narrowBump j) t +
        ∑ k ∈ S, if i = k then 0 else
          c i * c k * autocorr (narrowBump j) (t + x i - x k)) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = ∑ k ∈ S, ((if k = i then c i ^ 2 * autocorr (narrowBump j) t else 0) +
            (if i = k then 0 else c i * c k * autocorr (narrowBump j) (t + x i - x k))) :=
          Finset.sum_congr rfl fun k _ => he i k
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hi]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_mul, offCorrelation]

/-- A separated train has no off-diagonal correlation near the singular origin. -/
theorem offCorrelation_vanish_near_zero {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) (j : ℕ) {s t : ℝ}
    (hsep : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → s ≤ |x i - x k|)
    (ht : |t| + radius j < s) : offCorrelation S c x j t = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : i = k
  · exact if_pos hik
  · rw [if_neg hik, bump_autocorr_vanish, mul_zero]
    have htri : |x i - x k| ≤ |t + x i - x k| + |t| := by
      calc
        _ = |(t + x i - x k) - t| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    linarith [hsep i hi k hk hik]

/-- Off-diagonal correlations also vanish beyond the span plus the packet radius. -/
theorem offCorrelation_vanish_far {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) (j : ℕ) {D t : ℝ}
    (hspan : ∀ i ∈ S, ∀ k ∈ S, |x i - x k| ≤ D)
    (ht : D + radius j < |t|) : offCorrelation S c x j t = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : i = k
  · exact if_pos hik
  · rw [if_neg hik, bump_autocorr_vanish, mul_zero]
    have htri : |t| ≤ |t + x i - x k| + |x i - x k| := by
      calc
        _ = |(t + x i - x k) - (x i - x k)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    linarith [hspan i hi k hk]

theorem integrable_abs_bump_autocorr (j : ℕ) :
    Integrable (fun t => |autocorr (narrowBump j) t|) :=
  ((continuous_autocorr ((narrowBump j).contDiff.of_le (by norm_cast))
    (narrowBump j).hasCompactSupport).integrable_of_hasCompactSupport
      (hasCompactSupport_autocorr (narrowBump j).hasCompactSupport)).abs

private theorem integrable_abs_shifted_bump_autocorr (j : ℕ) (v : ℝ) :
    Integrable (fun t => |autocorr (narrowBump j) (t + v)|) :=
  (integrable_abs_bump_autocorr j).comp_add_right v

private theorem abs_offCorrelation_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) (j : ℕ) (t : ℝ) :
    |offCorrelation S c x j t| ≤
      ∑ i ∈ S, ∑ k ∈ S, |c i| * |c k| * |autocorr (narrowBump j) (t + (x i - x k))| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  by_cases hik : i = k
  · simp only [if_pos hik, abs_zero]
    positivity
  · simp only [if_neg hik, abs_mul, add_sub_assoc]
    exact le_rfl

/-- Uniform absolute off-diagonal mass; no separation assumption is needed for this bound. -/
theorem integral_abs_offCorrelation_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) (j : ℕ) :
    (∫ t, |offCorrelation S c x j t|) ≤
      2 * radius j * mass j * S.card * ∑ i ∈ S, c i ^ 2 := by
  let G : ℝ → ℝ := fun t =>
    ∑ i ∈ S, ∑ k ∈ S, |c i| * |c k| * |autocorr (narrowBump j) (t + (x i - x k))|
  have hterm (i k : ι) : Integrable (fun t =>
      |c i| * |c k| * |autocorr (narrowBump j) (t + (x i - x k))|) :=
    (integrable_abs_shifted_bump_autocorr j _).const_mul _
  have hG : Integrable G := integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun k _ => hterm i k
  have hb := norm_integral_le_of_norm_le hG
    (f := fun t => |offCorrelation S c x j t|) (Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_abs] using abs_offCorrelation_le S c x j t)
  have he : (∫ t, G t) = (∑ i ∈ S, |c i|) ^ 2 * ∫ t, |autocorr (narrowBump j) t| := by
    dsimp only [G]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hterm i k]
    calc
      _ = ∑ i ∈ S, ∑ k ∈ S, |c i| * |c k| * ∫ t, |autocorr (narrowBump j) t| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum _ fun k _ => hterm i k]
        apply Finset.sum_congr rfl
        intro k hk
        rw [integral_const_mul]
        exact congrArg (fun z => |c i| * |c k| * z)
          (integral_add_right_eq_self (fun t => |autocorr (narrowBump j) t|) (x i - x k))
      _ = _ := by
        simp only [sq, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => |c i|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sq_abs, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hL := integral_abs_bump_autocorr_le j
  have hfac : 0 ≤ 2 * radius j * mass j :=
    mul_nonneg (mul_nonneg (by norm_num) (radius_pos j).le) (mass_pos j).le
  calc
    _ ≤ ‖∫ t, |offCorrelation S c x j t|‖ := le_abs_self _
    _ ≤ ∫ t, G t := hb
    _ = (∑ i ∈ S, |c i|) ^ 2 * ∫ t, |autocorr (narrowBump j) t| := he
    _ ≤ (∑ i ∈ S, |c i|) ^ 2 * (2 * radius j * mass j) :=
      mul_le_mul_of_nonneg_left hL (sq_nonneg _)
    _ ≤ ((∑ i ∈ S, c i ^ 2) * S.card) * (2 * radius j * mass j) :=
      mul_le_mul_of_nonneg_right hcs hfac
    _ = _ := by ring

/-- Both poles and the complete Gamma term on a real source. -/
def archEnergy (f : ℝ → ℝ) : ℝ :=
  weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))

/-- The regular interaction kernel after cancellation of the diagonal. -/
def regularWeight (t : ℝ) : ℝ := 4 * Real.cosh (t / 2) - archLevySinhWeight t

private def archIntegrand (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (autocorr f 0 - autocorr f t) * archLevySinhWeight t +
    4 * autocorr f t * Real.cosh (t / 2)

private theorem archEnergy_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    archEnergy f = EF.gammaBracket 0 * autocorr f 0 + ∫ t in Ioi 0, archIntegrand f t := by
  simpa only [archEnergy, archIntegrand, archLevySinhWeight] using
    weilArchRe_eq_exactForm hf hfc

private theorem integrable_archIntegrand {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : IntegrableOn (archIntegrand f) (Ioi 0) := by
  have hc := continuous_autocorr hf hfc
  have hs := hasCompactSupport_autocorr hfc
  exact (integrableOn_biScaleLevyIntegrand hf hfc).add
    ((((continuous_const.mul hc).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hs.mul_left.mul_right)).integrableOn)

theorem integrable_offCorrelation {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) (j : ℕ) : Integrable (offCorrelation S c x j) := by
  have he : offCorrelation S c x j = fun t =>
      autocorr (train S c x j) t - (∑ i ∈ S, c i ^ 2) * autocorr (narrowBump j) t := by
    funext t
    linarith [autocorr_train_split S c x j t]
  rw [he]
  have hf := (contDiff_train S c x j).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hfc := hasCompactSupport_train S c x j
  have hb := (narrowBump j).contDiff.of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hbc := (narrowBump j).hasCompactSupport
  exact ((continuous_autocorr hf hfc).integrable_of_hasCompactSupport
    (hasCompactSupport_autocorr hfc)).sub
      (((continuous_autocorr hb hbc).integrable_of_hasCompactSupport
        (hasCompactSupport_autocorr hbc)).const_mul _)

/-- The singular diagonal cancels before integration, retaining both signed pole terms. -/
theorem archEnergy_train_calibration {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) (j : ℕ) {s : ℝ}
    (hsep : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → s ≤ |x i - x k|)
    (hr : radius j < s) :
    archEnergy (train S c x j) - (∑ i ∈ S, c i ^ 2) * archEnergy (narrowBump j) =
      ∫ t in Ioi 0, offCorrelation S c x j t * regularWeight t := by
  have hf := (contDiff_train S c x j).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hfc := hasCompactSupport_train S c x j
  have hb := (narrowBump j).contDiff.of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hbc := (narrowBump j).hasCompactSupport
  have hz : offCorrelation S c x j 0 = 0 :=
    offCorrelation_vanish_near_zero S c x j hsep (by simpa only [abs_zero, zero_add] using hr)
  have hmass : autocorr (train S c x j) 0 =
      (∑ i ∈ S, c i ^ 2) * autocorr (narrowBump j) 0 := by
    rw [autocorr_train_split, hz, add_zero]
  have hi : (∫ t in Ioi 0, archIntegrand (train S c x j) t) -
      (∑ i ∈ S, c i ^ 2) * (∫ t in Ioi 0, archIntegrand (narrowBump j) t) =
        ∫ t in Ioi 0, offCorrelation S c x j t * regularWeight t := by
    rw [← integral_const_mul, ← integral_sub (integrable_archIntegrand hf hfc)
      ((integrable_archIntegrand hb hbc).const_mul _)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [archIntegrand, regularWeight]
    rw [hmass, autocorr_train_split]
    ring
  rw [archEnergy_eq hf hfc, archEnergy_eq hb hbc, hmass]
  linear_combination hi

/-- An elementary envelope on the support of the off-diagonal correlation. -/
def archEnvelope (s D : ℝ) : ℝ := (2 / s + 4) * Real.exp ((D + 1) / 2)

theorem archEnvelope_nonneg {s : ℝ} (hs : 0 < s) (D : ℝ) : 0 ≤ archEnvelope s D := by
  unfold archEnvelope
  positivity

theorem regularWeight_bound {s D t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hlo : s / 2 ≤ t) (hhi : t ≤ D + 1) : |regularWeight t| ≤ archEnvelope s D := by
  have hsh : s / 2 ≤ Real.sinh t := hlo.trans (Real.self_le_sinh_iff.mpr ht.le)
  have hex : Real.exp (t / 2) ≤ Real.exp ((D + 1) / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hcosh : Real.cosh (t / 2) ≤ Real.exp ((D + 1) / 2) := by
    have hm : Real.exp (-(t / 2)) ≤ Real.exp (t / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.cosh_eq]
    linarith
  have hlevy : archLevySinhWeight t ≤ 2 / s * Real.exp ((D + 1) / 2) := by
    unfold archLevySinhWeight
    calc
      _ ≤ Real.exp (t / 2) / (s / 2) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith) hsh
      _ ≤ Real.exp ((D + 1) / 2) / (s / 2) :=
        div_le_div_of_nonneg_right hex (by linarith)
      _ = _ := by field_simp
  have hn := (archLevySinhWeight_pos ht).le
  have hc := (Real.cosh_pos (t / 2)).le
  unfold regularWeight archEnvelope
  calc
    _ ≤ |4 * Real.cosh (t / 2)| + |archLevySinhWeight t| := abs_sub _ _
    _ = 4 * Real.cosh (t / 2) + archLevySinhWeight t := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) hc), abs_of_nonneg hn]
    _ ≤ _ := by nlinarith [hlevy, hcosh]

/-- Complete archimedean calibration error, uniform over every coefficient vector. -/
theorem abs_archEnergy_train_calibration_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c x : ι → ℝ) (j : ℕ) {s D : ℝ} (hs : 0 < s)
    (hsep : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → s ≤ |x i - x k|)
    (hspan : ∀ i ∈ S, ∀ k ∈ S, |x i - x k| ≤ D)
    (hr : radius j ≤ s / 2) (hr1 : radius j ≤ 1) :
    |archEnergy (train S c x j) - (∑ i ∈ S, c i ^ 2) * archEnergy (narrowBump j)| ≤
      (2 * radius j * mass j * S.card * ∑ i ∈ S, c i ^ 2) * archEnvelope s D := by
  rw [archEnergy_train_calibration S c x j hsep (by linarith)]
  have hR := integrable_offCorrelation S c x j
  have hC := archEnvelope_nonneg hs D
  have hb := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    ((hR.abs.const_mul (archEnvelope s D)).integrableOn)
    (f := fun t => offCorrelation S c x j t * regularWeight t) ?_
  · simp only [Real.norm_eq_abs, integral_const_mul] at hb
    calc
      _ ≤ archEnvelope s D * ∫ t in Ioi 0, |offCorrelation S c x j t| := hb
      _ ≤ archEnvelope s D * ∫ t, |offCorrelation S c x j t| :=
        mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hR.abs (Filter.Eventually.of_forall fun t => abs_nonneg _)) hC
      _ ≤ archEnvelope s D *
          (2 * radius j * mass j * S.card * ∑ i ∈ S, c i ^ 2) :=
        mul_le_mul_of_nonneg_left (integral_abs_offCorrelation_le S c x j) hC
      _ = _ := mul_comm _ _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : offCorrelation S c x j t = 0
    · simp only [hz, abs_zero, zero_mul, mul_zero, le_refl]
    · have hlo : s / 2 ≤ t := by
        by_contra h
        exact hz (offCorrelation_vanish_near_zero S c x j hsep (by
          rw [abs_of_pos ht]
          linarith))
      have hhi : t ≤ D + 1 := by
        by_contra h
        exact hz (offCorrelation_vanish_far S c x j hspan (by
          rw [abs_of_pos ht]
          linarith))
      exact (mul_le_mul_of_nonneg_left (regularWeight_bound hs ht hlo hhi)
        (abs_nonneg _)).trans_eq (mul_comm _ _)

private def vonMangoldtAtom (n : ℕ) : ℝ :=
  if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0

private def primeAtomAtGap (t : ℝ) : ℝ :=
  ∑' n : ℕ, if Real.log n = t then vonMangoldtAtom n else 0

private theorem summable_atom_indicator (t : ℝ) :
    Summable fun n : ℕ => if Real.log n = t then vonMangoldtAtom n else 0 := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌈Real.exp t⌉₊ + 1)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  rw [if_neg]
  intro h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have he : (n : ℝ) = Real.exp t := by rw [← h, Real.exp_log (by linarith)]
  have hb : (n : ℝ) ≤ ⌈Real.exp t⌉₊ := he ▸ Nat.le_ceil _
  have hb' : n ≤ ⌈Real.exp t⌉₊ := by exact_mod_cast hb
  omega

/-- The actual complete Weil energy, with the von Mangoldt weights. -/
def fullEnergy (f : ℝ → ℝ) : ℝ :=
  (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re

private theorem real_weilTest (f : ℝ → ℝ) (t : ℝ) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) t = (autocorr f t : ℂ) := by
  simpa only [autocorr_neg, neg_neg] using (autocorr_eq_weilTest f (-t)).symm

/-- Exact real normalization of all three channels of the full Weil form. -/
theorem fullEnergy_eq (f : ℝ → ℝ) :
    fullEnergy f = archEnergy f - 2 * ∑' n : ℕ, vonMangoldtAtom n * autocorr f (Real.log n) := by
  have hp : (∑' n : ℕ, (vonMangoldtAtom n : ℂ) *
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (Real.log n) +
        EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (-Real.log n))) =
      ((2 * ∑' n : ℕ, vonMangoldtAtom n * autocorr f (Real.log n) : ℝ) : ℂ) := by
    calc
      _ = ∑' n : ℕ, ((2 * (vonMangoldtAtom n * autocorr f (Real.log n)) : ℝ) : ℂ) := by
        apply tsum_congr
        intro n
        rw [real_weilTest, real_weilTest, autocorr_neg]
        push_cast
        ring
      _ = _ := by rw [← Complex.ofReal_tsum, tsum_mul_left]
  unfold vonMangoldtAtom at hp
  unfold fullEnergy weilFullFunctional
  rw [hp]
  simp only [archEnergy, weilArchRe, Complex.add_re, Complex.sub_re,
    Complex.ofReal_re, vonMangoldtAtom]
  ring

theorem radius_le_half (j : ℕ) : radius j ≤ 1 / 2 := by
  unfold radius
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [show (0 : ℝ) ≤ j by positivity]

/-- A single canonical packet has no prime samples at any resolution. -/
theorem fullEnergy_bump (j : ℕ) : fullEnergy (narrowBump j) = archEnergy (narrowBump j) := by
  have hz : ∀ n : ℕ, vonMangoldtAtom n * autocorr (narrowBump j) (Real.log n) = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (show (2 : ℝ) ≤ n by exact_mod_cast hn)
      have hg : radius j < |Real.log (n : ℝ)| :=
        lt_of_lt_of_le (by linarith [radius_le_half j, WeilExcess.seventeen_div_twentyfive_lt_log_two])
          ((hl).trans (le_abs_self _))
      rw [bump_autocorr_vanish j hg, mul_zero]
    · simp only [vonMangoldtAtom, if_neg hn, zero_mul]
  rw [fullEnergy_eq]
  simp only [hz, tsum_zero, mul_zero, sub_zero]

/-- The odd source formed by the two copies of each integer logarithm. -/
def latticeTrain (N j : ℕ) (c : Fin N → ℝ) : ℝ → ℝ :=
  train Finset.univ (amplitude c) position j

def coefficientEnergy {N : ℕ} (c : Fin N → ℝ) : ℝ := ∑ a, c a ^ 2

theorem coefficientEnergy_nonneg {N : ℕ} (c : Fin N → ℝ) : 0 ≤ coefficientEnergy c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sum_amplitude_sq {N : ℕ} (c : Fin N → ℝ) :
    (∑ i : LatticeIndex N, amplitude c i ^ 2) = 2 * coefficientEnergy c := by
  simp [Fintype.sum_prod_type, amplitude, coefficientEnergy, two_mul, Finset.sum_add_distrib]

/-- All integer logarithms are sampled exactly once the common packet radius fits the lattice. -/
theorem latticeTrain_sample {N n : ℕ} (hn : 1 ≤ n) (j : ℕ) (c : Fin N → ℝ)
    (hr : radius j < 1 / (((N + 2 : ℕ) : ℝ) ^ 2 + 1)) :
    autocorr (latticeTrain N j c) (Real.log n) = mass j *
      ∑ i : LatticeIndex N, ∑ k : LatticeIndex N,
        if position i - position k = Real.log n then amplitude c i * amplitude c k else 0 := by
  rw [latticeTrain, autocorr_train, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : position i - position k = Real.log n
  · have he : Real.log n + position k - position i = 0 := by linarith
    rw [if_pos h, he, bump_autocorr_zero]
    ring
  · have hg := hr.trans_le (lag_gap hn i k h)
    have hg' : radius j < |Real.log n + position k - position i| := by
      rw [show Real.log n + position k - position i = Real.log n - position i + position k by
        ring]
      exact hg
    rw [if_neg h, bump_autocorr_vanish j hg', mul_zero, mul_zero]

/-- The selected prime quadratic form before folding the two lattice copies. -/
def selectedAtomForm {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ i : LatticeIndex N, ∑ k : LatticeIndex N,
    amplitude c i * amplitude c k * primeAtomAtGap (position i - position k)

/-- Exact simultaneous summation of the selected prime atoms. -/
theorem primePairing_latticeTrain {N : ℕ} (j : ℕ) (c : Fin N → ℝ)
    (hr : radius j < 1 / (((N + 2 : ℕ) : ℝ) ^ 2 + 1)) :
    (∑' n : ℕ, vonMangoldtAtom n * autocorr (latticeTrain N j c) (Real.log n)) =
      mass j * selectedAtomForm c := by
  let T : LatticeIndex N → LatticeIndex N → ℕ → ℝ := fun i k n =>
    amplitude c i * amplitude c k *
      (if Real.log n = position i - position k then vonMangoldtAtom n else 0)
  have hT (i k : LatticeIndex N) : Summable (T i k) :=
    (summable_atom_indicator (position i - position k)).mul_left _
  have he (n : ℕ) : vonMangoldtAtom n * autocorr (latticeTrain N j c) (Real.log n) =
      mass j * ∑ i : LatticeIndex N, ∑ k : LatticeIndex N, T i k n := by
    by_cases hn : 1 ≤ n
    · rw [latticeTrain_sample hn j c hr]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [T]
      by_cases h : position i - position k = Real.log n
      · rw [if_pos h, if_pos h.symm]
        ring
      · rw [if_neg h, if_neg (Ne.symm h)]
        ring
    · have hn0 : n = 0 := by omega
      subst n
      simp [vonMangoldtAtom, T]
  rw [tsum_congr he, tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun k _ => hT i k)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum fun k _ => hT i k]
  apply Finset.sum_congr rfl
  intro k hk
  exact tsum_mul_left

private theorem atomAt_eq_zero_of_neg {t : ℝ} (ht : t < 0) : primeAtomAtGap t = 0 := by
  unfold primeAtomAtGap
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rw [if_neg]
  intro h
  have hn := Real.log_natCast_nonneg n
  linarith

private theorem atomAt_log_nat {m : ℕ} (hm : 1 ≤ m) :
    primeAtomAtGap (Real.log m) = vonMangoldtAtom m := by
  unfold primeAtomAtGap
  rw [tsum_eq_single m]
  · rw [if_pos rfl]
  · intro n hn
    split_ifs with h
    · rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp [vonMangoldtAtom]
      · exfalso
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        exact hn (by exact_mod_cast Real.log_injOn_pos hnR hmR h)
    · rfl

private theorem atomAt_log_sub_log {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    primeAtomAtGap (Real.log b - Real.log a) =
      if a ∣ b then vonMangoldtAtom (b / a) else 0 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  split_ifs with hab
  · obtain ⟨m, rfl⟩ := hab
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hb
      · exact h
    rw [Nat.mul_div_cancel_left m (by omega), Nat.cast_mul,
      Real.log_mul haR.ne' (by exact_mod_cast (by omega : m ≠ 0)), add_sub_cancel_left,
      atomAt_log_nat hm]
  · unfold primeAtomAtGap
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [if_neg]
    intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [Nat.cast_zero, Real.log_zero] at h
      have he : (b : ℝ) = a := Real.log_injOn_pos hbR haR (by linarith)
      exact hab ⟨1, by rw [mul_one]; exact_mod_cast he⟩
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have he : Real.log ((n : ℝ) * a) = Real.log b := by
        rw [Real.log_mul hnR.ne' haR.ne', h]
        ring
      have he' : (n : ℝ) * a = b := Real.log_injOn_pos
        (show (0 : ℝ) < (n : ℝ) * a from mul_pos hnR haR) hbR he
      exact hab ⟨n, by rw [mul_comm]; exact_mod_cast he'.symm⟩

private theorem atomAt_log_add_log {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    primeAtomAtGap (Real.log a + Real.log b) = vonMangoldtAtom (a * b) := by
  rw [← log_nat_mul ha hb, atomAt_log_nat (Nat.mul_le_mul ha hb)]

/-- The signed ratio/product incidence form on the integer labels `2, ..., N+1`. -/
def incidenceForm {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∑ a, ∑ b, c a * c b *
    ((if b.val + 2 ∣ a.val + 2 then vonMangoldtAtom ((a.val + 2) / (b.val + 2)) else 0) +
      (if a.val + 2 ∣ b.val + 2 then vonMangoldtAtom ((b.val + 2) / (a.val + 2)) else 0) -
        vonMangoldtAtom ((a.val + 2) * (b.val + 2)))

private theorem signed_pair_sum {N : ℕ} (c : Fin N → ℝ) (a b : Fin N) :
    (∑ u : Bool, ∑ v : Bool, amplitude c (a, u) * amplitude c (b, v) *
      primeAtomAtGap (position (a, u) - position (b, v))) = c a * c b *
        ((if b.val + 2 ∣ a.val + 2 then vonMangoldtAtom ((a.val + 2) / (b.val + 2)) else 0) +
          (if a.val + 2 ∣ b.val + 2 then vonMangoldtAtom ((b.val + 2) / (a.val + 2)) else 0) -
            vonMangoldtAtom ((a.val + 2) * (b.val + 2))) := by
  have ha : 1 ≤ a.val + 2 := by omega
  have hb : 1 ≤ b.val + 2 := by omega
  have hla : 0 < Real.log (a.val + 2 : ℕ) := log_label_pos (a, true)
  have hlb : 0 < Real.log (b.val + 2 : ℕ) := log_label_pos (b, true)
  have hneg : -Real.log (a.val + 2 : ℕ) - Real.log (b.val + 2 : ℕ) =
      -(Real.log (a.val + 2 : ℕ) + Real.log (b.val + 2 : ℕ)) := by ring
  have hrev : -Real.log (a.val + 2 : ℕ) + Real.log (b.val + 2 : ℕ) =
      Real.log (b.val + 2 : ℕ) - Real.log (a.val + 2 : ℕ) := by ring
  simp only [Fintype.sum_bool, amplitude, position_eq, label, Bool.false_eq_true,
    ↓reduceIte, sub_neg_eq_add]
  rw [hneg, hrev, atomAt_eq_zero_of_neg (by linarith :
    -(Real.log (a.val + 2 : ℕ) + Real.log (b.val + 2 : ℕ)) < 0),
    atomAt_log_sub_log ha hb, atomAt_log_sub_log hb ha, atomAt_log_add_log ha hb]
  ring

/-- Folding the two copies retains both same-side ratios and the crossing product. -/
theorem selectedAtomForm_eq {N : ℕ} (c : Fin N → ℝ) : selectedAtomForm c = incidenceForm c := by
  unfold selectedAtomForm incidenceForm
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  exact signed_pair_sum c a b

/-- The complete lattice energy has its exact prime matrix, with no prime asymptotic. -/
theorem fullEnergy_latticeTrain {N : ℕ} (j : ℕ) (c : Fin N → ℝ)
    (hr : radius j < 1 / (((N + 2 : ℕ) : ℝ) ^ 2 + 1)) :
    fullEnergy (latticeTrain N j c) =
      archEnergy (latticeTrain N j c) - 2 * mass j * incidenceForm c := by
  rw [fullEnergy_eq, primePairing_latticeTrain j c hr, selectedAtomForm_eq]
  ring

/-- A resolution that controls all prime resonances and all regular interactions. -/
def resolution (N k : ℕ) : ℕ := 128 * (N + 2) ^ 4 * (k + 1)

private theorem resolution_cast (N k : ℕ) :
    (resolution N k : ℝ) = 128 * ((N + 2 : ℕ) : ℝ) ^ 4 * ((k : ℝ) + 1) := by
  simp only [resolution, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_one]

theorem radius_resolution_le (N k : ℕ) :
    radius (resolution N k) ≤ (1 / (((N + 2 : ℕ) : ℝ) ^ 2 + 1)) / 2 := by
  let L : ℝ := N + 2
  have hL : 2 ≤ L := by dsimp only [L]; linarith [show (0 : ℝ) ≤ N by positivity]
  have hL2 : 4 ≤ L ^ 2 := by nlinarith only [hL]
  have hpow : L ^ 2 ≤ L ^ 4 := by nlinarith only [hL2, sq_nonneg (L ^ 2 - 1)]
  have hk : 1 ≤ 128 * ((k : ℝ) + 1) := by linarith [show (0 : ℝ) ≤ k by positivity]
  have hprod := mul_le_mul_of_nonneg_left hk (show 0 ≤ L ^ 4 by positivity)
  have hj : L ^ 2 ≤ (resolution N k : ℝ) := by
    rw [resolution_cast]
    push_cast
    dsimp only [L] at hpow hprod
    nlinarith only [hpow, hprod]
  unfold radius
  calc
    _ ≤ 1 / (2 * (((N + 2 : ℕ) : ℝ) ^ 2 + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by
        push_cast at *
        dsimp only [L] at hj
        linarith only [hj])
    _ = _ := by rw [div_div, mul_comm (2 : ℝ)]

private theorem resolution_error_scale (N k : ℕ) :
    64 * radius (resolution N k) * ((N + 2 : ℕ) : ℝ) ^ 4 ≤ 1 / ((k : ℝ) + 1) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hL : 0 ≤ ((N + 2 : ℕ) : ℝ) ^ 4 := by positivity
  have hd : 0 < 128 * ((N + 2 : ℕ) : ℝ) ^ 4 * ((k : ℝ) + 1) + 1 := by positivity
  have he : 64 * radius (resolution N k) * ((N + 2 : ℕ) : ℝ) ^ 4 =
      (32 * ((N + 2 : ℕ) : ℝ) ^ 4) /
        (128 * ((N + 2 : ℕ) : ℝ) ^ 4 * ((k : ℝ) + 1) + 1) := by
    unfold radius
    rw [resolution_cast]
    field_simp
    ring
  rw [he, div_le_div_iff₀ hd hk]
  nlinarith only [mul_nonneg hL hk.le]

private theorem lattice_archEnvelope_le (N : ℕ) :
    archEnvelope (1 / (((N + 2 : ℕ) : ℝ) ^ 2 + 1))
      (2 * Real.log (N + 2 : ℕ)) ≤ 8 * ((N + 2 : ℕ) : ℝ) ^ 3 := by
  let L : ℝ := (N + 2 : ℕ)
  have hL : 2 ≤ L := by dsimp only [L]; exact_mod_cast (show 2 ≤ N + 2 by omega)
  have hL0 : 0 < L := by linarith only [hL]
  have hL2 : 4 ≤ L ^ 2 := by nlinarith only [hL]
  -- `exp (1/2) ≤ exp (log 2) = 2`, since `1/2 < 17/25 < log 2`.
  have hex : Real.exp (1 / 2 : ℝ) ≤ 2 :=
    calc Real.exp (1 / 2 : ℝ) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith [WeilExcess.seventeen_div_twentyfive_lt_log_two])
      _ = 2 := Real.exp_log (by norm_num)
  have he : Real.exp ((2 * Real.log L + 1) / 2) = L * Real.exp (1 / 2) := by
    rw [show (2 * Real.log L + 1) / 2 = Real.log L + 1 / 2 by ring,
      Real.exp_add, Real.exp_log hL0]
  change (2 / (1 / (L ^ 2 + 1)) + 4) * Real.exp ((2 * Real.log L + 1) / 2) ≤ _
  rw [he, div_div_eq_mul_div, div_one]
  calc
    _ ≤ (2 * (L ^ 2 + 1) + 4) * (L * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hex hL0.le) (by positivity)
    _ ≤ 8 * L ^ 3 := by
      nlinarith only [mul_le_mul_of_nonneg_right hL2 hL0.le, hL0]

/-- The singular self-energy is common to all packets; its removal has a uniform small error. -/
theorem archEnergy_latticeTrain_error (N k : ℕ) (c : Fin N → ℝ) :
    |archEnergy (latticeTrain N (resolution N k) c) -
        2 * coefficientEnergy c * archEnergy (narrowBump (resolution N k))| ≤
      mass (resolution N k) * coefficientEnergy c / ((k : ℝ) + 1) := by
  let j := resolution N k
  let L : ℝ := (N + 2 : ℕ)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hN : (N : ℝ) ≤ L := by dsimp only [L]; push_cast; linarith
  have hE := coefficientEnergy_nonneg c
  have hM := (mass_pos j).le
  have hr := (radius_pos j).le
  have hs : 0 < 1 / (L ^ 2 + 1) := by positivity
  have hb := abs_archEnergy_train_calibration_le Finset.univ (amplitude c) position j hs
    (fun i _ l _ hil => position_gap i l hil)
    (fun i _ l _ => position_span i l)
    (radius_resolution_le N k) ((radius_le_half j).trans (by norm_num))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_ofNat, sum_amplitude_sq, ← latticeTrain.eq_1] at hb
  calc
    _ ≤ (2 * radius j * mass j * ((N : ℝ) * 2) * (2 * coefficientEnergy c)) *
        archEnvelope (1 / (L ^ 2 + 1)) (2 * Real.log L) := hb
    _ ≤ (2 * radius j * mass j * ((N : ℝ) * 2) * (2 * coefficientEnergy c)) *
        (8 * L ^ 3) :=
      mul_le_mul_of_nonneg_left (lattice_archEnvelope_le N) (by positivity)
    _ ≤ (2 * radius j * mass j * (L * 2) * (2 * coefficientEnergy c)) *
        (8 * L ^ 3) := by gcongr
    _ = (64 * radius j * L ^ 4) * (mass j * coefficientEnergy c) := by ring
    _ ≤ (1 / ((k : ℝ) + 1)) * (mass j * coefficientEnergy c) :=
      mul_le_mul_of_nonneg_right (resolution_error_scale N k) (mul_nonneg hM hE)
    _ = _ := by ring

/-- Full-Weil finite-part bridge, simultaneously for every lattice size and coefficient vector. -/
theorem fullEnergy_latticeTrain_uniform (N k : ℕ) (c : Fin N → ℝ) :
    |(fullEnergy (latticeTrain N (resolution N k) c) -
          2 * coefficientEnergy c * fullEnergy (narrowBump (resolution N k))) /
        mass (resolution N k) + 2 * incidenceForm c| ≤ coefficientEnergy c / ((k : ℝ) + 1) := by
  let j := resolution N k
  have hm := mass_pos j
  have hs : 0 < 1 / (((N + 2 : ℕ) : ℝ) ^ 2 + 1) := by positivity
  have hr : radius j < 1 / (((N + 2 : ℕ) : ℝ) ^ 2 + 1) := by
    linarith [radius_resolution_le N k]
  have he : (fullEnergy (latticeTrain N j c) -
        2 * coefficientEnergy c * fullEnergy (narrowBump j)) / mass j + 2 * incidenceForm c =
      (archEnergy (latticeTrain N j c) -
        2 * coefficientEnergy c * archEnergy (narrowBump j)) / mass j := by
    rw [fullEnergy_latticeTrain j c hr, fullEnergy_bump]
    field_simp [hm.ne']
    ring
  change |(fullEnergy (latticeTrain N j c) -
    2 * coefficientEnergy c * fullEnergy (narrowBump j)) / mass j + 2 * incidenceForm c| ≤ _
  rw [he, abs_div, abs_of_pos hm, div_le_iff₀ hm]
  calc
    _ ≤ mass j * coefficientEnergy c / ((k : ℝ) + 1) := archEnergy_latticeTrain_error N k c
    _ = _ := by ring

end RHTower.ArithmeticIncidenceBump

end

