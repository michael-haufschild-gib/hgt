import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeCanonicalSystem
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.HeckeSimilitudesOfAWindowAreScalars
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.InfiniteGenusLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer

/-!
# The Schur parameters of Spec ℤ

Fix a real `C²` compactly supported bump `φ ≠ 0` and a step `h > 0`. The lattice translates
`T_k = φ(· + kh)` (`latticeTranslate`) span the **lattice tests** `Σ_k x_kT_k` (`latticeTest`), and
translation invariance of Weil's pairing makes their Gram form Toeplitz:

`Q(Σ_k x_kT_k) = Σ_{j,k} κ(j − k)x_jx_k`, `κ(d) = W(φ, φ(· + dh))` (`weilQuad_latticeTest`),

with `κ` even (`weilSeq_isEven`): the **Weil sequence** of `φ` at step `h`, the orbit correlation of
`φ` (AOG) sampled on `hℤ`. The lattice canonical system of `TheLatticeCanonicalSystem` applies:
margins `E_n(φ, h)`, Schur parameters `β_n(φ, h)`, reflection coefficients `γ_n(φ, h)`.

* **Translates are independent** (`latticeTest_ne_zero`): a nonzero amplitude vector gives a nonzero
  lattice test (look at the leftmost translate at the left edge of the support of `φ`).
* **RH as a causal evolution** (`riemannHypothesis_iff_levinsonErr_pos`,
  `riemannHypothesis_iff_abs_reflCoeff_lt_one`): RH holds iff for every bump and every step all
  lattice margins are positive, iff `Q(φ) > 0` and every lattice reflection coefficient of Spec ℤ
  lies in `(−1, 1)`. Each new lattice site is a stage; it is admitted iff the newest Weil datum
  `κ(n + 1)` lands in the prediction interval `(π_n − E_n, π_n + E_n)` of the frozen data.
* **Degenerate windows refute RH** (`not_riemannHypothesis_of_first_critical`): if a lattice window is
  positive definite and the next margin vanishes, the Levinson vector gives a nonzero window test
  with `Q = 0`, a palindrome up to sign with nonzero ends; under RH Weil's form is positive definite,
  so no lattice of Spec ℤ ever degenerates.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ SpacingScaleHarmonicAnalysis
  ArithmeticCastelnuovoSeveri

variable {φ : ℝ → ℝ} {h : ℝ}

/-! ### Lattice translates and the Weil sequence -/

/-- The translate `φ(· + kh)` of a bump to the lattice site `k`. -/
def latticeTranslate (φ : ℝ → ℝ) (h : ℝ) (k : ℤ) : ℝ → ℝ := fun u => φ (u + k * h)

/-- The **Weil sequence** of `φ` at step `h`: `κ(d) = W(φ, φ(· + dh))`. -/
def weilSeq (φ : ℝ → ℝ) (h : ℝ) (d : ℤ) : ℝ := weilPair φ (latticeTranslate φ h d)

/-- The **lattice test** with amplitudes `x`: `Σ_k x_kφ(· + kh)`. -/
def latticeTest (φ : ℝ → ℝ) (h : ℝ) {n : ℕ} (x : Fin n → ℝ) : ℝ → ℝ :=
  ∑ k : Fin n, x k • latticeTranslate φ h k

theorem latticeTest_apply {n : ℕ} (x : Fin n → ℝ) (u : ℝ) :
    latticeTest φ h x u = ∑ k : Fin n, x k * φ (u + (k : ℕ) * h) := by
  simp [latticeTest, latticeTranslate, Finset.sum_apply, smul_eq_mul]

theorem latticeTranslate_zero (φ : ℝ → ℝ) (h : ℝ) : latticeTranslate φ h 0 = φ := by
  funext u; simp [latticeTranslate]

theorem latticeTranslate_mem (hφ : φ ∈ realTests) (h : ℝ) (k : ℤ) :
    latticeTranslate φ h k ∈ realTests :=
  ⟨hφ.1.comp (contDiff_id.add contDiff_const),
    hφ.2.comp_homeomorph (Homeomorph.addRight ((k : ℝ) * h))⟩

theorem latticeTest_mem (hφ : φ ∈ realTests) {n : ℕ} (x : Fin n → ℝ) :
    latticeTest φ h x ∈ realTests :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (latticeTranslate_mem hφ h k)

/-- Translation invariance: `W(T_i, T_j) = κ(j − i)`. -/
theorem weilPair_latticeTranslate (φ : ℝ → ℝ) (h : ℝ) (i j : ℤ) :
    weilPair (latticeTranslate φ h i) (latticeTranslate φ h j) = weilSeq φ h (j - i) := by
  have e := weilPair_comp_sub φ (latticeTranslate φ h (j - i)) (-((i : ℝ) * h))
  have e1 : (fun u => φ (u - -((i : ℝ) * h))) = latticeTranslate φ h i := by
    funext u; simp only [latticeTranslate, sub_neg_eq_add]
  have e2 : (fun u => latticeTranslate φ h (j - i) (u - -((i : ℝ) * h))) =
      latticeTranslate φ h j := by
    funext u; simp only [latticeTranslate]; push_cast; ring_nf
  rw [e1, e2] at e
  exact e

/-- **The Weil sequence is even.** -/
theorem weilSeq_isEven (φ : ℝ → ℝ) (h : ℝ) : IsEvenSeq (weilSeq φ h) := by
  intro d
  have e := weilPair_latticeTranslate φ h d 0
  rw [zero_sub, latticeTranslate_zero, weilPair_comm] at e
  rw [← e, weilSeq]

/-- Weil's pairing is additive over finite sums in the first argument. -/
theorem weilPair_sum_left {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i, f i ∈ realTests) {g : ℝ → ℝ} (hg : g ∈ realTests) :
    weilPair (∑ i ∈ s, f i) g = ∑ i ∈ s, weilPair (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have := weilPair_smul_left 0 g g
    simpa using this
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha,
      weilPair_add_left (hf a) (Submodule.sum_mem _ fun i _ => hf i) hg, ih]

/-- **The lattice Gram form is Toeplitz**: `Q(Σ_k x_kT_k) = Σ_{j,k} κ(j − k)x_jx_k`. -/
theorem weilQuad_latticeTest (hφ : φ ∈ realTests) (h : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    weilQuad (latticeTest φ h x) = toeplitzForm (weilSeq φ h) n x := by
  have hT : ∀ k : Fin n, x k • latticeTranslate φ h k ∈ realTests := fun k =>
    Submodule.smul_mem _ _ (latticeTranslate_mem hφ h k)
  have hL : (∑ k : Fin n, x k • latticeTranslate φ h k) ∈ realTests := latticeTest_mem hφ x
  show weilPair (∑ k : Fin n, x k • latticeTranslate φ h k)
    (∑ k : Fin n, x k • latticeTranslate φ h k) = _
  rw [weilPair_sum_left _ hT hL, toeplitzForm]
  refine sum_congr rfl fun i _ => ?_
  rw [weilPair_smul_left, weilPair_comm, weilPair_sum_left _ hT (latticeTranslate_mem hφ h i),
    mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [weilPair_smul_left, weilPair_latticeTranslate]
  ring

/-! ### Translates are linearly independent -/

/-- **Lattice translates are independent**: a nonzero amplitude vector gives a nonzero lattice test. -/
theorem latticeTest_ne_zero (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0) (hh : 0 < h) {n : ℕ}
    {x : Fin n → ℝ} (hx : x ≠ 0) : latticeTest φ h x ≠ 0 := by
  classical
  -- the left edge `s` of the support of `φ`
  set S : Set ℝ := {u | φ u ≠ 0}
  have hSne : S.Nonempty := by
    by_contra hS
    exact hφ0 (funext fun u => by
      by_contra hu
      exact hS ⟨u, hu⟩)
  have hSbdd : BddBelow S := by
    obtain ⟨R, hR⟩ := hφ.2.isCompact.isBounded.subset_closedBall 0
    refine ⟨-R, fun u hu => ?_⟩
    have := hR (subset_tsupport φ hu)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [neg_abs_le u]
  set s := sInf S
  have hbelow : ∀ w, w < s → φ w = 0 := fun w hw => by
    by_contra hw'
    exact absurd (csInf_le hSbdd hw') (not_le.mpr hw)
  obtain ⟨v, hvS, hv⟩ := exists_lt_of_csInf_lt hSne (lt_add_of_pos_right s hh)
  have hvs : s ≤ v := csInf_le hSbdd hvS
  -- the leftmost active site `K`
  set A : Finset (Fin n) := univ.filter fun k => x k ≠ 0
  have hAne : A.Nonempty := by
    by_contra hA
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hA
    exact hx (funext fun k => by simpa using hA (Finset.mem_univ k))
  set K := A.max' hAne
  have hK : x K ≠ 0 := (mem_filter.mp (A.max'_mem hAne)).2
  have hgt : ∀ k : Fin n, K < k → x k = 0 := fun k hk => by
    by_contra hk'
    exact absurd (A.le_max' k (mem_filter.mpr ⟨Finset.mem_univ k, hk'⟩)) (not_le.mpr hk)
  intro h0
  have hval := congrFun h0 (v - (K : ℕ) * h)
  rw [latticeTest_apply, Pi.zero_apply, sum_eq_single K] at hval
  · rw [show v - (K : ℕ) * h + (K : ℕ) * h = v by ring] at hval
    exact mul_ne_zero hK hvS hval
  · intro k _ hkK
    rcases lt_or_gt_of_ne hkK with hk | hk
    · have hk' : ((k : ℕ) : ℝ) + 1 ≤ (K : ℕ) := by exact_mod_cast hk
      rw [hbelow _ (by nlinarith), mul_zero]
    · rw [hgt k hk, zero_mul]
  · exact fun h => absurd (Finset.mem_univ K) h

/-! ### RH as a causal evolution -/

/-- **Under RH every lattice window of Spec ℤ is positive definite.** -/
theorem toeplitzPosDef_of_riemannHypothesis (hRH : RiemannHypothesis) (hφ : φ ∈ realTests)
    (hφ0 : φ ≠ 0) (hh : 0 < h) (n : ℕ) : ToeplitzPosDef (weilSeq φ h) n := by
  intro x hx
  rw [← weilQuad_latticeTest hφ h x]
  have hL := latticeTest_mem (h := h) hφ x
  have hne := latticeTest_ne_zero hφ hφ0 hh hx
  rw [LogCells.weilQuad_eq_zetaW hL.1 hL.2]
  exact riemannHypothesis_iff_weil_positive_definite.mp hRH _ (cx_contDiff hL.1)
    (cx_hasCompactSupport hL.2) fun hc => hne (funext fun u => by simpa using congrFun hc u)

/-- **RH is the positivity of every lattice margin of Spec ℤ.** -/
theorem riemannHypothesis_iff_levinsonErr_pos :
    RiemannHypothesis ↔
      ∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h → ∀ n : ℕ, 0 < levinsonErr (weilSeq φ h) n := by
  constructor
  · intro hRH φ hφ hφ0 h hh n
    exact (toeplitzForm_posDef_iff (weilSeq_isEven φ h) n).mp
      (toeplitzPosDef_of_riemannHypothesis hRH hφ hφ0 hh (n + 1)) n le_rfl
  · intro hE
    rw [ArithmeticHodgeTheoryOfDegenerations.riemannHypothesis_iff_weilQuad_nonneg]
    intro g hg hgc
    by_cases hg0 : g = 0
    · rw [hg0]
      have := weilPair_smul_left 0 (0 : ℝ → ℝ) (0 : ℝ → ℝ)
      simp only [zero_smul, zero_mul] at this
      exact this.ge
    · have h0 := hE g ⟨hg, hgc⟩ hg0 1 one_pos 0
      rw [levinsonErr_zero, weilSeq, latticeTranslate_zero] at h0
      exact h0.le

/-- **RH is the confinement of every lattice reflection coefficient of Spec ℤ to `(−1, 1)`.** -/
theorem riemannHypothesis_iff_abs_reflCoeff_lt_one :
    RiemannHypothesis ↔
      ∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h →
        0 < weilQuad φ ∧ ∀ n : ℕ, |reflCoeff (weilSeq φ h) n| < 1 := by
  rw [riemannHypothesis_iff_levinsonErr_pos]
  refine forall_congr' fun φ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun h => forall_congr' fun _ => ?_
  rw [levinsonErr_pos_iff]
  rw [weilSeq, latticeTranslate_zero]
  rfl

/-- **A degenerate lattice window refutes RH.** If a lattice window of Spec ℤ is positive definite
and the next margin vanishes, the Levinson vector gives a nonzero test of Weil energy zero. -/
theorem not_riemannHypothesis_of_first_critical (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0) (hh : 0 < h)
    {n : ℕ} (hpd : ToeplitzPosDef (weilSeq φ h) (n + 1))
    (h0 : levinsonErr (weilSeq φ h) (n + 1) = 0) : ¬RiemannHypothesis := by
  intro hRH
  have hk := (toeplitzForm_kernel_of_first_critical (weilSeq_isEven φ h) hpd h0).2
    (levinsonVec (weilSeq φ h) (n + 1))
  have hv : levinsonVec (weilSeq φ h) (n + 1) ≠ 0 := fun hc => by
    simpa [levinsonVec] using congrFun hc 0
  have hpos := toeplitzPosDef_of_riemannHypothesis hRH hφ hφ0 hh (n + 2) _ hv
  have hz : toeplitzForm (weilSeq φ h) (n + 2) (levinsonVec (weilSeq φ h) (n + 1)) = 0 :=
    hk.mpr (funext fun k => by simp [levinsonVec])
  linarith

end GaloisForLFunctions.GrowingWindowsOfSpecZ
