import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheFrobeniusLadderIsMetzler
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm

/-!
# The atomic form of `ζ` is Metzler below the spacing

Atomic tests `f_x = Σ_{n ≤ N} x_n g(· − log n)` with a nonnegative bump `g` supported in `[0, w]`.
Weil's form on them is `Q(f) = M(f) + 2C(f)² − 2S(f)²` with the Markov form
`M = 2θ′(0)‖·‖² + levyEnergy − primeSum` (SpacingScaleHarmonicAnalysis). Its polar form is the
**Markov pairing** (`markovPair`), symmetric and bilinear on compactly supported `C²` tests, so on
the atomic family `M(f_x) = Σ_{m,n} x_m x_n M(g_m, g_n)` (`levyMarkovForm_atomicTest_eq`).

* **Separated atoms meet nonpositively** (`markovPair_atom_nonpos`): if `|log n − log m| > w`,
  then `∫ g_m g_n = 0`, the Lévy cross integrand `(g_m − g_m(·+y))(g_n − g_n(·+y))` is
  pointwise `−g_m g_n(·+y) − g_m(·+y) g_n ≤ 0`, and the prime pairing is a sum of nonnegative
  terms. In the Euler gauge every off-diagonal entry of the Markov Gram is `≤ 0`.
* **The atomic intersection form is Metzler below the spacing**
  (`atomicIntersectionGram_isMetzler`): for `w < δ_N` the Gram of `H, V, g_1, …, g_N` — pole plane,
  pole row `(∫ g_n e^{−u/2}, ∫ g_n e^{u/2})`, atom block `−M(g_m, g_n)` — has nonnegative
  off-diagonal entries; it is connected through `H` and has a positive weight with positive image.
* **Weil positivity below the spacing is the trickle-down inequality**
  (`weilQuad_atomicTest_nonneg_iff_weightedTrickleDown`): by the block Hodge index theorem the
  Gram is hyperbolic iff `Q(f_x) ≥ 0` for every `x`, and by the weighted Metzler Hodge index theorem
  this holds iff `(TD_π)` holds.

The sign hypothesis of Lorentzian theory is therefore satisfied by `ζ` itself on separated atomic
families, and nothing else is: the remaining content of Weil positivity there is exactly the
trickle-down inequality.
-/

noncomputable section

open MeasureTheory Set Finset Matrix RHTower
open scoped Real

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

/-! ### The Markov pairing -/

/-- The atom `g(· − log n)`. -/
def atom (g : ℝ → ℝ) (n : ℕ) (u : ℝ) : ℝ := g (u - Real.log n)

/-- The prime pairing `Σ_k Λ_k (∫ f(t) d(t − log k) + ∫ f(t) d(t + log k))`. -/
def primePair (f d : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, vonMangoldtAtom k * ((∫ t, f t * d (t - Real.log k)) + ∫ t, f t * d (t + Real.log k))

/-- The **Markov pairing**, the polar form of `levyMarkovForm`. -/
def markovPair (f d : ℝ → ℝ) : ℝ :=
  2 * gammaHardyPhaseRate 0 * (∫ u, f u * d u) + (∫ y in Ioi 0, levyMixed f d y) - primePair f d

theorem markovPair_self (f : ℝ → ℝ) : markovPair f f = levyMarkovForm f := by
  unfold markovPair levyMarkovForm levyMixed primePair levyEnergy primeSum
  simp only [← sq]

theorem primePair_comm (f d : ℝ → ℝ) : primePair f d = primePair d f := by
  unfold primePair
  refine tsum_congr fun k => ?_
  congr 1
  have e1 : ∫ t, f t * d (t - Real.log k) = ∫ t, d t * f (t + Real.log k) := by
    rw [← integral_add_right_eq_self (fun t => f t * d (t - Real.log k)) (Real.log k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [add_sub_cancel_right]; ring)
  have e2 : ∫ t, f t * d (t + Real.log k) = ∫ t, d t * f (t - Real.log k) := by
    rw [← integral_sub_right_eq_self (fun t => f t * d (t + Real.log k)) (Real.log k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [sub_add_cancel]; ring)
  rw [e1, e2, add_comm]

theorem markovPair_comm (f d : ℝ → ℝ) : markovPair f d = markovPair d f := by
  unfold markovPair levyMixed
  rw [primePair_comm]
  congr 2
  · congr 1; exact integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)
  · refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)

/-- On tests supported in `[−R, R]` the prime pairing is a finite sum. -/
theorem primePair_eq_sum_of_supportedIn {R : ℝ} {f d : ℝ → ℝ} (hf : SupportedIn R f)
    (hd : SupportedIn R d) :
    primePair f d = ∑ k ∈ Finset.range (lagRange R), vonMangoldtAtom k *
      ((∫ t, f t * d (t - Real.log k)) + ∫ t, f t * d (t + Real.log k)) := by
  rw [primePair]
  refine tsum_eq_sum fun k hk => ?_
  have hk' : lagRange R ≤ k := by simpa using hk
  have hl := two_mul_lt_abs_log_of_lagRange_le hk'
  have e1 : ∀ t, f t * d (t - Real.log k) = 0 := fun t => by
    rw [sub_eq_add_neg]
    exact mul_shift_eq_zero_of_supportedIn hf hd (by rwa [abs_neg]) t
  have e2 : ∀ t, f t * d (t + Real.log k) = 0 := fun t => mul_shift_eq_zero_of_supportedIn hf hd hl t
  simp [e1, e2]

theorem integrable_mul_shift {f d : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hd : Continuous d) (c : ℝ) : Integrable fun t => f t * d (t + c) :=
  (hf.mul (hd.comp (continuous_add_const c))).integrable_of_hasCompactSupport hfc.mul_right

theorem supportedIn_sum {ι : Type*} (s : Finset ι) {R : ℝ} {d : ι → ℝ → ℝ}
    (hdR : ∀ i, SupportedIn R (d i)) (x : ι → ℝ) : SupportedIn R fun u => ∑ i ∈ s, x i * d i u :=
  fun u hu => sum_eq_zero fun i _ => by rw [hdR i u hu, mul_zero]

/-- **Linearity in the second argument** over finite sums of `C²` tests supported in `[−R, R]`. -/
theorem markovPair_sum_right {ι : Type*} (s : Finset ι) {R : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hfR : SupportedIn R f) {d : ι → ℝ → ℝ}
    (hd : ∀ i, ContDiff ℝ 2 (d i)) (hdc : ∀ i, HasCompactSupport (d i))
    (hdR : ∀ i, SupportedIn R (d i)) (x : ι → ℝ) :
    markovPair f (fun u => ∑ i ∈ s, x i * d i u) = ∑ i ∈ s, x i * markovPair f (d i) := by
  -- the `L²` pairing
  have h1 : ∫ u, f u * ∑ i ∈ s, x i * d i u = ∑ i ∈ s, x i * ∫ u, f u * d i u := by
    simp_rw [mul_sum]
    rw [integral_finsetSum _ fun i _ => by
      simpa [mul_left_comm] using
        (integrable_mul_shift hf.continuous hfc (hd i).continuous 0).const_mul (x i)]
    refine sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  -- the Lévy cross energy
  have h2 : ∫ y in Ioi 0, levyMixed f (fun u => ∑ i ∈ s, x i * d i u) y =
      ∑ i ∈ s, x i * ∫ y in Ioi 0, levyMixed f (d i) y := by
    have hpt : ∀ y, levyMixed f (fun u => ∑ i ∈ s, x i * d i u) y =
        ∑ i ∈ s, x i * levyMixed f (d i) y := fun y => by
      unfold levyMixed
      have e : ∀ u, (f u - f (u + y)) * (∑ i ∈ s, x i * d i u - ∑ i ∈ s, x i * d i (u + y)) =
          ∑ i ∈ s, x i * ((f u - f (u + y)) * (d i u - d i (u + y))) := fun u => by
        rw [← sum_sub_distrib, mul_sum]
        exact sum_congr rfl fun i _ => by ring
      simp_rw [e]
      rw [integral_finsetSum _ fun i _ =>
        (integrable_sub_shift_mul hf.continuous hfc (hd i).continuous y).const_mul (x i), mul_sum]
      exact sum_congr rfl fun i _ => by rw [integral_const_mul]; ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ =>
      ((integrableOn_levyMixed hf hfc (hd i) (hdc i)).const_mul (x i))]
    exact sum_congr rfl fun i _ => integral_const_mul _ _
  -- the prime pairing
  have h3 : primePair f (fun u => ∑ i ∈ s, x i * d i u) = ∑ i ∈ s, x i * primePair f (d i) := by
    rw [primePair_eq_sum_of_supportedIn hfR (supportedIn_sum s hdR x)]
    simp_rw [primePair_eq_sum_of_supportedIn hfR (hdR _)]
    have e : ∀ c : ℝ, ∫ t, f t * ∑ i ∈ s, x i * d i (t + c) =
        ∑ i ∈ s, x i * ∫ t, f t * d i (t + c) := fun c => by
        simp_rw [mul_sum]
        rw [integral_finsetSum _ fun i _ => by
          simpa [mul_left_comm] using
            (integrable_mul_shift hf.continuous hfc (hd i).continuous c).const_mul (x i)]
        refine sum_congr rfl fun i _ => ?_
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
    simp_rw [sub_eq_add_neg, e, mul_sum, ← sum_add_distrib, mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring
  unfold markovPair
  rw [h1, h2, h3]
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-! ### The Markov Gram of the atomic family -/

variable {g : ℝ → ℝ} {w : ℝ}

theorem contDiff_atom (hg : ContDiff ℝ 2 g) (n : ℕ) : ContDiff ℝ 2 (atom g n) :=
  hg.comp (contDiff_id.sub contDiff_const)

theorem hasCompactSupport_atom (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (n : ℕ) :
    HasCompactSupport (atom g n) := by
  have := hasCompactSupport_atomicTest (g := g) hgsupp n (fun k => if k = n then 1 else 0)
  refine HasCompactSupport.intro (K := Set.Icc (Real.log n) (Real.log n + w)) isCompact_Icc
    fun u hu => hgsupp _ fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The atoms `n ≤ N` lie in the window `[−R, R]`, `R = log N + w + 1`. -/
theorem supportedIn_atom (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) {N n : ℕ}
    (hn : n ∈ Finset.Icc 1 N) : SupportedIn (Real.log N + w + 1) (atom g n) := by
  intro u hu
  apply hgsupp
  rintro ⟨h1, h2⟩
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN)
  have : |u| ≤ Real.log N + w := by
    rw [abs_le]; constructor <;> linarith
  linarith

theorem atomicTest_eq_sum_atom (N : ℕ) (x : ℕ → ℝ) (g : ℝ → ℝ) :
    atomicTest N x g = fun u => ∑ n ∈ Finset.Icc 1 N, x n * atom g n u := rfl

/-- **The Markov form of a finite combination is the quadratic form of the Markov Gram.** -/
theorem levyMarkovForm_sum_eq {ι : Type*} (s : Finset ι) {R : ℝ} {e : ι → ℝ → ℝ}
    (he : ∀ i, ContDiff ℝ 2 (e i)) (hec : ∀ i, HasCompactSupport (e i))
    (heR : ∀ i, SupportedIn R (e i)) (x : ι → ℝ) :
    levyMarkovForm (fun u => ∑ i ∈ s, x i * e i u) =
      ∑ i ∈ s, ∑ j ∈ s, x i * x j * markovPair (e i) (e j) := by
  have hF : ContDiff ℝ 2 fun u => ∑ i ∈ s, x i * e i u :=
    ContDiff.sum fun i _ => contDiff_const.mul (he i)
  have hFc : HasCompactSupport fun u => ∑ i ∈ s, x i * e i u :=
    HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc fun u hu =>
      supportedIn_sum s heR x u (by
        by_contra h; push Not at h; exact hu (abs_le.mp h))
  rw [← markovPair_self, markovPair_sum_right _ hF hFc (supportedIn_sum s heR x) he hec heR]
  refine sum_congr rfl fun i _ => ?_
  rw [markovPair_comm, markovPair_sum_right _ (he i) (hec i) (heR i) he hec heR, mul_sum]
  exact sum_congr rfl fun j _ => by rw [markovPair_comm]; ring

/-- **The Markov form of an atomic test is the quadratic form of the Markov Gram.** -/
theorem levyMarkovForm_atomicTest_eq (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (N : ℕ) (x : ℕ → ℝ) :
    levyMarkovForm (atomicTest N x g) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, x m * x n * markovPair (atom g m) (atom g n) := by
  set R := Real.log N + w + 1
  have hR : ∀ n, SupportedIn R (if n ∈ Finset.Icc 1 N then atom g n else fun _ => 0) := fun n => by
    split_ifs with h
    · exact supportedIn_atom hgsupp hw h
    · intro u _; rfl
  -- restrict the atoms to the window so that one support bound serves every index
  set d : ℕ → ℝ → ℝ := fun n => if n ∈ Finset.Icc 1 N then atom g n else fun _ => 0
  have hd : ∀ n, ContDiff ℝ 2 (d n) := fun n => by
    simp only [d]; split_ifs
    · exact contDiff_atom hg n
    · exact contDiff_const
  have hdc : ∀ n, HasCompactSupport (d n) := fun n => by
    simp only [d]; split_ifs
    · exact hasCompactSupport_atom hgsupp n
    · exact HasCompactSupport.zero
  have hF : atomicTest N x g = fun u => ∑ n ∈ Finset.Icc 1 N, x n * d n u := by
    funext u
    exact sum_congr rfl fun n hn => by simp only [d, if_pos hn]; rfl
  have hFR : SupportedIn R (atomicTest N x g) := by rw [hF]; exact supportedIn_sum _ hR x
  have hFd := contDiff_atomicTest hg N x
  have hFc := hasCompactSupport_atomicTest hgsupp N x
  rw [← markovPair_self]
  conv_lhs => rw [show atomicTest N x g = fun u => ∑ n ∈ Finset.Icc 1 N, x n * d n u from hF]
  rw [markovPair_sum_right _ (by rw [← hF]; exact hFd) (by rw [← hF]; exact hFc)
    (by rw [← hF]; exact hFR) hd hdc hR]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun n hn => ?_
  rw [markovPair_comm, markovPair_sum_right _ (hd n) (hdc n) (hR n) hd hdc hR, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  simp only [d, if_pos hm, if_pos hn]
  rw [markovPair_comm]; ring

/-! ### Separated atoms meet nonpositively -/

/-- **Separated atoms meet nonpositively.** For a nonnegative bump supported in `[0, w]` and atoms
at log-distance `> w`, the Markov pairing is `≤ 0`: the overlap vanishes, the Lévy cross integrand
is pointwise `≤ 0`, and the prime pairing is nonnegative. -/
theorem markovPair_atom_nonpos (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {m n : ℕ} (hsep : w < |Real.log n - Real.log m|) :
    markovPair (atom g m) (atom g n) ≤ 0 := by
  -- disjoint supports
  have hdisj : ∀ u, atom g m u * atom g n u = 0 := fun u => by
    by_contra h
    have hm : u - Real.log m ∈ Set.Icc 0 w := by
      by_contra h'; exact h (by simp [atom, hgsupp _ h'])
    have hn : u - Real.log n ∈ Set.Icc 0 w := by
      by_contra h'; exact h (by simp [atom, hgsupp _ h'])
    have : |Real.log n - Real.log m| ≤ w := by
      rw [abs_le]; constructor <;> linarith [hm.1, hm.2, hn.1, hn.2]
    linarith
  have h1 : ∫ u, atom g m u * atom g n u = 0 := by simp [hdisj]
  have h2 : ∫ y in Ioi 0, levyMixed (atom g m) (atom g n) y ≤ 0 := by
    refine setIntegral_nonpos measurableSet_Ioi fun y hy => ?_
    unfold levyMixed
    refine mul_nonpos_of_nonneg_of_nonpos (RHTower.archLevyDensity_pos hy).le ?_
    have hpt : ∀ u, (atom g m u - atom g m (u + y)) * (atom g n u - atom g n (u + y)) ≤ 0 :=
      fun u => by
        have e : (atom g m u - atom g m (u + y)) * (atom g n u - atom g n (u + y)) =
            -(atom g m u * atom g n (u + y)) - atom g m (u + y) * atom g n u := by
          have := hdisj u; have := hdisj (u + y); nlinarith
        rw [e]
        have := mul_nonneg (hg0 (u - Real.log m)) (hg0 (u + y - Real.log n))
        have := mul_nonneg (hg0 (u + y - Real.log m)) (hg0 (u - Real.log n))
        simp only [atom] at *
        linarith
    exact integral_nonpos hpt
  have h3 : 0 ≤ primePair (atom g m) (atom g n) := by
    refine tsum_nonneg fun k => mul_nonneg (RHTower.vonMangoldtAtom_nonneg' k) (add_nonneg ?_ ?_) <;>
      exact integral_nonneg fun t => mul_nonneg (hg0 _) (hg0 _)
  unfold markovPair
  rw [h1, mul_zero, zero_add]
  linarith

/-! ### The atomic intersection Gram -/

/-- The Markov Gram of the atoms `1, …, N`. -/
def atomicMarkovGram (g : ℝ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => markovPair (atom g ((i : ℕ) + 1)) (atom g ((j : ℕ) + 1))

/-- The pole row `(∫ g_n e^{−u/2}, ∫ g_n e^{u/2})` of the atoms. -/
def atomPoleRow (g : ℝ → ℝ) (N : ℕ) : Matrix (Fin 2) (Fin N) ℝ :=
  Matrix.of fun a j =>
    ∫ u, atom g ((j : ℕ) + 1) u * (if a = 0 then Real.exp (-(u / 2)) else Real.exp (u / 2))

/-- The intersection Gram of `H, V, g_1, …, g_N`: pole plane, pole row and `−M(g_m, g_n)`. -/
def atomicIntersectionGram (g : ℝ → ℝ) (N : ℕ) :
    Matrix (Fin 2 ⊕ Fin N) (Fin 2 ⊕ Fin N) ℝ :=
  fromBlocks realPolePlane (atomPoleRow g N) (atomPoleRow g N)ᵀ (-atomicMarkovGram g N)

theorem atomicMarkovGram_isSymm (g : ℝ → ℝ) (N : ℕ) : (atomicMarkovGram g N).IsSymm :=
  Matrix.IsSymm.ext fun i j => by simp only [atomicMarkovGram, Matrix.of_apply, markovPair_comm]

theorem atomicIntersectionGram_isSymm (g : ℝ → ℝ) (N : ℕ) :
    (atomicIntersectionGram g N).IsSymm := by
  unfold atomicIntersectionGram Matrix.IsSymm
  rw [fromBlocks_transpose, transpose_transpose, transpose_neg, (atomicMarkovGram_isSymm g N).eq]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem mem_Icc_succ {N : ℕ} (j : Fin N) : (j : ℕ) + 1 ∈ Finset.Icc 1 N :=
  Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- **The atomic intersection form is Metzler below the spacing** (Euler gauge, `g ≥ 0`). -/
theorem atomicIntersectionGram_isMetzler (hg0 : ∀ u, 0 ≤ g u)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hw : w < atomSpacing N) :
    IsMetzler (atomicIntersectionGram g N) := by
  intro a b hab
  rcases a with a | i <;> rcases b with b | j
  · fin_cases a <;> fin_cases b <;> simp_all [atomicIntersectionGram, realPolePlane]
  · simp only [atomicIntersectionGram, fromBlocks_apply₁₂, atomPoleRow, Matrix.of_apply]
    refine integral_nonneg fun u => mul_nonneg (hg0 _) ?_
    split_ifs <;> exact (Real.exp_pos _).le
  · simp only [atomicIntersectionGram, fromBlocks_apply₂₁, transpose_apply, atomPoleRow,
      Matrix.of_apply]
    refine integral_nonneg fun u => mul_nonneg (hg0 _) ?_
    split_ifs <;> exact (Real.exp_pos _).le
  · simp only [atomicIntersectionGram, fromBlocks_apply₂₂, Matrix.neg_apply, atomicMarkovGram,
      Matrix.of_apply, neg_nonneg]
    have hij : (i : ℕ) + 1 ≠ (j : ℕ) + 1 := fun h => hab (by
      congr 1; exact Fin.ext (by omega))
    have := atomSpacing_le_abs_logGap (mem_Icc_succ i) (mem_Icc_succ j) hij
    exact markovPair_atom_nonpos hg0 hgsupp (by rw [logGap] at this; push_cast at this ⊢; linarith)

theorem atomPoleRow_zero_pos (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u)
    {u₀ : ℝ} (hu₀ : 0 < g u₀) {N : ℕ} (j : Fin N) : 0 < atomPoleRow g N 0 j := by
  simp only [atomPoleRow, Matrix.of_apply, if_true]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := u₀ + Real.log ((j : ℕ) + 1 : ℕ))
    ((hg.comp (continuous_id.sub continuous_const)).mul (Real.continuous_exp.comp
      (continuous_id.div_const 2).neg))
    ((hgc.comp_homeomorph (Homeomorph.subRight _)).mul_right) (fun u => mul_nonneg (hg0 _)
      (Real.exp_pos _).le) ?_
  simp only [atom, add_sub_cancel_right]
  exact mul_ne_zero hu₀.ne' (Real.exp_pos _).ne'

/-! ### Two lemmas on Grams with a hyperbolic pole plane -/

variable {κ : Type*} [Fintype κ]

omit [Fintype κ] in
/-- A pole-plane Gram whose `H`-row is positive has connected support. -/
theorem poleGram_isConnectedSupport (B : Matrix (Fin 2) κ ℝ) (L : Matrix κ κ ℝ)
    (hB : ∀ j, B 0 j ≠ 0) : IsConnectedSupport (fromBlocks realPolePlane B Bᵀ L) := by
  intro w hw
  have hH : ∀ j, w j = w (Sum.inl 0) := by
    rintro (a | k)
    · fin_cases a
      · rfl
      · exact (hw (Sum.inl 0) (Sum.inl 1) (by simp [realPolePlane])).symm
    · exact (hw (Sum.inl 0) (Sum.inr k) (by simpa using hB k)).symm
  intro j k; rw [hH j, hH k]

/-- The weight `(t, t, 1, …, 1)`. -/
def poleWeight (B : Matrix (Fin 2) κ ℝ) (L : Matrix κ κ ℝ) : Fin 2 ⊕ κ → ℝ :=
  Sum.elim (fun _ => (1 + ∑ k, ∑ l, |L k l|) * (1 + ∑ k, (B 0 k)⁻¹)) fun _ => 1

/-- **A pole-plane Gram with a positive `H`-row is in the trickle-down regime.** -/
theorem poleWeight_pos_and_mulVec_pos (B : Matrix (Fin 2) κ ℝ) (L : Matrix κ κ ℝ)
    (hB0 : ∀ j, 0 < B 0 j) (hB1 : ∀ j, 0 ≤ B 1 j) :
    (∀ i, 0 < poleWeight B L i) ∧ ∀ i, 0 < (fromBlocks realPolePlane B Bᵀ L *ᵥ poleWeight B L) i := by
  set T := ∑ k, ∑ l, |L k l|
  set S := ∑ k, (B 0 k)⁻¹
  have hT : 0 ≤ T := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hS : 0 ≤ S := sum_nonneg fun k _ => (inv_pos.mpr (hB0 k)).le
  have ht : 0 < (1 + T) * (1 + S) := by positivity
  refine ⟨fun i => by
    rcases i with a | k
    · exact ht
    · simp [poleWeight], fun i => ?_⟩
  rw [show poleWeight B L = Sum.elim (fun _ => (1 + T) * (1 + S)) (fun _ => 1) from rfl,
    fromBlocks_mulVec]
  rcases i with a | k
  · simp only [Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.add_apply]
    fin_cases a
    · simp only [realPolePlane, mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, mul_one, zero_mul, one_mul,
        zero_add]
      have : 0 ≤ ∑ x, B 0 x := sum_nonneg fun j _ => (hB0 j).le
      linarith
    · simp only [realPolePlane, mulVec, dotProduct, Fin.sum_univ_two]
      simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero,
        mul_one]
      have : 0 ≤ ∑ x, B 1 x := sum_nonneg fun j _ => hB1 j
      linarith
  · simp only [Sum.elim_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.add_apply, mulVec, dotProduct,
      transpose_apply, Fin.sum_univ_two, mul_one]
    have hrow : -T ≤ ∑ l, L k l := by
      have h1 : ∑ l, -|L k l| ≤ ∑ l, L k l := sum_le_sum fun l _ => neg_abs_le _
      have h2 : ∑ l, |L k l| ≤ T :=
        single_le_sum (f := fun k => ∑ l, |L k l|) (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
          (mem_univ k)
      rw [sum_neg_distrib] at h1; linarith
    have hSk : (B 0 k)⁻¹ ≤ S := single_le_sum (f := fun k => (B 0 k)⁻¹)
      (fun k _ => (inv_pos.mpr (hB0 k)).le) (mem_univ k)
    have hkey : 1 + T ≤ B 0 k * ((1 + T) * (1 + S)) := by
      have h1 : 1 ≤ B 0 k * (1 + S) := by
        have := mul_le_mul_of_nonneg_left hSk (hB0 k).le
        rw [mul_inv_cancel₀ (hB0 k).ne'] at this
        nlinarith [hB0 k]
      nlinarith
    have : 0 ≤ B 1 k * ((1 + T) * (1 + S)) := mul_nonneg (hB1 k) ht.le
    linarith

/-! ### Weil positivity below the spacing is the trickle-down inequality -/

/-- The atomic test `Σ_{j < N} d_j g(· − log (j + 1))`. -/
def finAtomicTest (g : ℝ → ℝ) (N : ℕ) (d : Fin N → ℝ) (u : ℝ) : ℝ :=
  ∑ j, d j * atom g ((j : ℕ) + 1) u

theorem sum_Icc_one_eq_sum_fin (N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ j : Fin N, f ((j : ℕ) + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => f (j + 1)) N, range_eq_Ico,
    show Finset.Icc 1 N = (Finset.Ico 0 N).map (addRightEmbedding 1) by
      rw [map_add_right_Ico]; ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, sum_map]
  rfl

/-- `finAtomicTest` is the corpus' `atomicTest` with the coefficients shifted to `1, …, N`. -/
theorem finAtomicTest_eq_atomicTest (g : ℝ → ℝ) (N : ℕ) (d : Fin N → ℝ) :
    finAtomicTest g N d =
      atomicTest N (fun n => if h : 1 ≤ n ∧ n ≤ N then d ⟨n - 1, by omega⟩ else 0) g := by
  funext u
  rw [atomicTest, sum_Icc_one_eq_sum_fin]
  refine sum_congr rfl fun j _ => ?_
  rw [dif_pos ⟨by omega, by omega⟩]
  simp only [atom, Nat.add_sub_cancel, Fin.eta]

theorem integral_finAtomicTest_mul {φ : ℝ → ℝ} (hφ : Continuous φ) (hg : Continuous g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (d : Fin N → ℝ) :
    ∫ u, finAtomicTest g N d u * φ u = ∑ j, d j * ∫ u, atom g ((j : ℕ) + 1) u * φ u := by
  simp only [finAtomicTest, sum_mul]
  rw [integral_finsetSum _ fun j _ => ?_]
  · exact sum_congr rfl fun j _ => by rw [← integral_const_mul]; congr 1; funext u; ring
  · refine ((continuous_const.mul (hg.comp (continuous_id.sub continuous_const))).mul hφ)
      |>.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_right (HasCompactSupport.mul_left ?_)
    exact hasCompactSupport_atom hgsupp _

/-- **The polar defect of the atomic intersection Gram is Weil's form.** -/
theorem polarDefect_atomic (hg : ContDiff ℝ 2 g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw0 : 0 ≤ w) (N : ℕ) (d : Fin N → ℝ) :
    polarDefect (atomPoleRow g N) (-atomicMarkovGram g N) d = weilQuad (finAtomicTest g N d) := by
  set f := finAtomicTest g N d
  have hfc : ContDiff ℝ 2 f := ContDiff.sum fun j _ => contDiff_const.mul (contDiff_atom hg _)
  have hfR : SupportedIn (Real.log N + w + 1) f :=
    supportedIn_sum _ (fun j => supportedIn_atom hgsupp hw0 (mem_Icc_succ j)) d
  have hfcs : HasCompactSupport f :=
    HasCompactSupport.intro (K := Set.Icc (-(Real.log N + w + 1)) (Real.log N + w + 1))
      isCompact_Icc fun u hu => hfR u (by
        by_contra h; push Not at h; exact hu (abs_le.mp h))
  -- the pole moments
  have hB0 : (atomPoleRow g N *ᵥ d) 0 = ∫ u, f u * Real.exp (-(u / 2)) := by
    rw [integral_finAtomicTest_mul (φ := fun u => Real.exp (-(u / 2))) (by fun_prop)
      hg.continuous hgsupp]
    simp only [mulVec, dotProduct, atomPoleRow, Matrix.of_apply, if_true]
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hB1 : (atomPoleRow g N *ᵥ d) 1 = ∫ u, f u * Real.exp (u / 2) := by
    rw [integral_finAtomicTest_mul (φ := fun u => Real.exp (u / 2)) (by fun_prop)
      hg.continuous hgsupp]
    simp only [mulVec, dotProduct, atomPoleRow, Matrix.of_apply, one_ne_zero, if_false]
    exact sum_congr rfl fun j _ => mul_comm _ _
  -- the Markov part
  have hM : qf (-atomicMarkovGram g N) d = -levyMarkovForm f := by
    rw [show f = fun u => ∑ j, d j * atom g ((j : ℕ) + 1) u from rfl,
      levyMarkovForm_sum_eq _ (fun j => contDiff_atom hg _) (fun j => hasCompactSupport_atom hgsupp _)
        (fun j => supportedIn_atom hgsupp hw0 (mem_Icc_succ j)), qf_eq_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [Matrix.neg_apply, atomicMarkovGram, Matrix.of_apply]
    ring
  -- the pole term of Weil's form
  have hint : ∀ φ : ℝ → ℝ, Continuous φ → Integrable fun u => f u * φ u := fun φ hφ =>
    (hfc.continuous.mul hφ).integrable_of_hasCompactSupport hfcs.mul_right
  have hCS : 2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2 =
      2 * (∫ u, f u * Real.exp (-(u / 2))) * ∫ u, f u * Real.exp (u / 2) := by
    have hc := hint (fun u => Real.cosh (u / 2)) (by fun_prop)
    have hs := hint (fun u => Real.sinh (u / 2)) (by fun_prop)
    have e1 : ∫ u, f u * Real.exp (-(u / 2)) = coshHalfMoment f - sinhHalfMoment f := by
      rw [coshHalfMoment, sinhHalfMoment, ← integral_sub hc hs]
      congr 1; funext u; rw [← mul_sub, Real.cosh_sub_sinh]
    have e2 : ∫ u, f u * Real.exp (u / 2) = coshHalfMoment f + sinhHalfMoment f := by
      rw [coshHalfMoment, sinhHalfMoment, ← integral_add hc hs]
      congr 1; funext u; rw [← mul_add, Real.cosh_add_sinh]
    rw [e1, e2]; ring
  rw [polarDefect, hB0, hB1, hM, weilQuad_eq hfc hfcs, hCS]
  unfold levyMarkovForm
  ring

/-- **Hodge index on the atomic family ⇔ Weil positivity.** -/
theorem atomicIntersectionGram_isHyperbolic_iff (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 ≤ w) (N : ℕ) :
    IsHyperbolic (atomicIntersectionGram g N) ↔ ∀ d, 0 ≤ weilQuad (finAtomicTest g N d) := by
  have hL : (-atomicMarkovGram g N).IsSymm := by
    unfold Matrix.IsSymm; rw [transpose_neg, (atomicMarkovGram_isSymm g N).eq]
  rw [atomicIntersectionGram, isHyperbolic_fromBlocks_iff _ hL]
  simp_rw [polarDefect_atomic hg hgsupp hw0]

/-- **Weil positivity below the spacing is the trickle-down inequality.** For a nonnegative,
nonzero `C²` bump supported in `[0, w]` with `w < δ_N`, the Euler-gauge atomic intersection Gram is
Metzler, connected and in the trickle-down regime, and Weil's form is nonnegative on the atomic
family iff the Gram satisfies `(TD_π)`. -/
theorem weilQuad_finAtomicTest_nonneg_iff_weightedTrickleDown (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hg0 : ∀ u, 0 ≤ g u) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {u₀ : ℝ} (hu₀ : 0 < g u₀) (hw0 : 0 ≤ w) {N : ℕ} (hw : w < atomSpacing N) :
    (∀ d, 0 ≤ weilQuad (finAtomicTest g N d)) ↔
      WeightedTrickleDown (poleWeight (atomPoleRow g N) (-atomicMarkovGram g N))
        (atomicIntersectionGram g N) := by
  have hB0 := atomPoleRow_zero_pos hg.continuous hgc hg0 hu₀ (N := N)
  have hB1 : ∀ j, 0 ≤ atomPoleRow g N 1 j := fun j => by
    simp only [atomPoleRow, Matrix.of_apply, one_ne_zero, if_false]
    exact integral_nonneg fun u => mul_nonneg (hg0 _) (Real.exp_pos _).le
  obtain ⟨hπ, hQπ⟩ := poleWeight_pos_and_mulVec_pos (atomPoleRow g N) (-atomicMarkovGram g N)
    hB0 hB1
  rw [← atomicIntersectionGram_isHyperbolic_iff hg hgsupp hw0]
  exact isHyperbolic_iff_weightedTrickleDown (atomicIntersectionGram_isSymm g N)
    (atomicIntersectionGram_isMetzler hg0 hgsupp hw)
    (poleGram_isConnectedSupport _ _ fun j => (hB0 j).ne') hπ hQπ

end GaloisForLFunctions.ArithmeticLorentzianGeometry
