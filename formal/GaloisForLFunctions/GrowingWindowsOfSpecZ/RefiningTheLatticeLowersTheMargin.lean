import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheSchurParametersOfSpecZ

/-!
# Refining the lattice lowers the margin

The margin `E_n` of a lattice window is the minimum of the Toeplitz form over amplitude vectors with
first coordinate `1` (`levinsonErr_le_toeplitzForm`, `toeplitzForm_levinsonVec`). A lattice of step
`h` is contained in the lattice of step `h/k`: its translates are every `k`-th translate of the finer
lattice (`latticeTest_refineVec`). Hence (`levinsonErr_refine_le`)

`E_{kn}(φ, h/k) ≤ E_n(φ, h)`:

refining the lattice adds interior directions over the same total length and can only lower the
margin. Along the dyadic refinements `h/2^j` of a fixed total length the margins of Spec ℤ form a
nonincreasing sequence of positive numbers under RH (`levinsonErr_dyadic_antitone`), and converge
(`tendsto_levinsonErr_dyadic`): this limit is the margin of the continuum window, the first step of
the continuum limit of the lattice canonical system.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri

variable {κ : ℤ → ℝ}

/-- The Levinson vector realizes the margin: `T_{n+1}(1, a^{(n)}) = E_n`. -/
theorem toeplitzForm_levinsonVec (hκ : IsEvenSeq κ) {n : ℕ}
    (h : ∀ k < n, levinsonErr κ k ≠ 0) : toeplitzForm κ (n + 1) (levinsonVec κ n) = levinsonErr κ n := by
  rw [levinsonVec, toeplitzForm_cons hκ (levinson_isPredictor hκ h), predErr_levinson hκ h]
  simp [toeplitzForm]

/-- **The margin is a minimum**: if the window of size `n` is positive definite, every vector with
first coordinate `1` has energy at least `E_n`. -/
theorem levinsonErr_le_toeplitzForm (hκ : IsEvenSeq κ) {n : ℕ} (hpd : ToeplitzPosDef κ n)
    (h : ∀ k < n, levinsonErr κ k ≠ 0) (z : Fin n → ℝ) :
    levinsonErr κ n ≤ toeplitzForm κ (n + 1) (Fin.cons 1 z) := by
  rw [toeplitzForm_cons hκ (levinson_isPredictor hκ h), predErr_levinson hκ h, one_pow, mul_one]
  have : 0 ≤ toeplitzForm κ n (fun k => z k - 1 * levinsonPred κ n k) := by
    by_cases h0 : (fun k => z k - 1 * levinsonPred κ n k) = 0
    · rw [h0]; simp [toeplitzForm]
    · exact (hpd _ h0).le
  linarith

/-- The amplitude vector of a coarse lattice placed on every `k`-th site of the fine lattice. -/
def refineVec (k : ℕ) {n : ℕ} (x : Fin (n + 1) → ℝ) : Fin (k * n + 1) → ℝ := fun j =>
  if hj : k ∣ (j : ℕ) ∧ (j : ℕ) / k < n + 1 then x ⟨(j : ℕ) / k, hj.2⟩ else 0

theorem refineVec_zero (k : ℕ) {n : ℕ} (x : Fin (n + 1) → ℝ) : refineVec k x 0 = x 0 := by
  simp [refineVec]

/-- **The coarse lattice sits inside the fine one**: `Σ_j y_jφ(· + jh/k) = Σ_i x_iφ(· + ih)`. -/
theorem latticeTest_refineVec (φ : ℝ → ℝ) (h : ℝ) {k : ℕ} (hk : 0 < k) {n : ℕ}
    (x : Fin (n + 1) → ℝ) : latticeTest φ (h / k) (refineVec k x) = latticeTest φ h x := by
  funext u
  rw [latticeTest_apply, latticeTest_apply]
  -- the sum over the fine lattice reduces to the multiples of `k`
  have hinj : ∀ i : Fin (n + 1), k * (i : ℕ) < k * n + 1 := fun i => by
    have := i.isLt; nlinarith
  let emb : Fin (n + 1) → Fin (k * n + 1) := fun i => ⟨k * i, hinj i⟩
  have hemb : Function.Injective emb := fun i j hij => by
    have : k * (i : ℕ) = k * j := congrArg Fin.val hij
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hk this)
  symm
  set f : Fin (k * n + 1) → ℝ := fun j => refineVec k x j * φ (u + ((j : ℕ) : ℝ) * (h / k))
  have hzero : ∀ j ∈ (univ : Finset (Fin (k * n + 1))), j ∉ univ.image emb → f j = 0 := by
    intro j _ hj
    have hnd : ¬ (k ∣ (j : ℕ) ∧ (j : ℕ) / k < n + 1) := by
      rintro ⟨⟨c, hc⟩, hc2⟩
      apply hj
      refine mem_image.mpr ⟨⟨c, ?_⟩, mem_univ _, Fin.ext ?_⟩
      · rw [hc, Nat.mul_div_cancel_left _ hk] at hc2; exact hc2
      · simp [emb, hc]
    simp only [f, refineVec, dif_neg hnd, zero_mul]
  rw [← sum_subset (subset_univ (univ.image emb)) hzero,
    sum_image fun i _ j _ hij => hemb hij]
  refine sum_congr rfl fun i _ => ?_
  have hd : k ∣ k * (i : ℕ) ∧ k * (i : ℕ) / k < n + 1 := by
    rw [Nat.mul_div_cancel_left _ hk]; exact ⟨dvd_mul_right _ _, i.isLt⟩
  simp only [f, emb, refineVec, dif_pos hd]
  have hi : (⟨k * (i : ℕ) / k, hd.2⟩ : Fin (n + 1)) = i := Fin.ext (Nat.mul_div_cancel_left _ hk)
  rw [hi]
  congr 2
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

/-- **Refining the lattice lowers the margin**: if the fine lattice window of size `kn` is positive
definite, `E_{kn}(φ, h/k) ≤ E_n(φ, h)`. -/
theorem levinsonErr_refine_le {φ : ℝ → ℝ} (hφ : φ ∈ realTests) (h : ℝ) {k : ℕ} (hk : 0 < k)
    {n : ℕ} (hfine : ToeplitzPosDef (weilSeq φ (h / k)) (k * n))
    (hcoarse : ∀ j < n, levinsonErr (weilSeq φ h) j ≠ 0) :
    levinsonErr (weilSeq φ (h / k)) (k * n) ≤ levinsonErr (weilSeq φ h) n := by
  have hκf := weilSeq_isEven φ (h / k)
  have hκc := weilSeq_isEven φ h
  -- the fine margins are positive up to `kn − 1`
  have hfne : ∀ j < k * n, levinsonErr (weilSeq φ (h / k)) j ≠ 0 := by
    intro j hj
    obtain ⟨m, hm⟩ : ∃ m, k * n = m + 1 := ⟨k * n - 1, by omega⟩
    rw [hm] at hfine
    exact ((toeplitzForm_posDef_iff hκf m).mp hfine j (by omega)).ne'
  have hle := levinsonErr_le_toeplitzForm hκf hfine hfne
    (Fin.tail (refineVec k (levinsonVec (weilSeq φ h) n)))
  have hcons : (Fin.cons 1 (Fin.tail (refineVec k (levinsonVec (weilSeq φ h) n))) :
      Fin (k * n + 1) → ℝ) = refineVec k (levinsonVec (weilSeq φ h) n) := by
    conv_rhs => rw [← Fin.cons_self_tail (refineVec k (levinsonVec (weilSeq φ h) n))]
    rw [refineVec_zero]
    simp [levinsonVec]
  rw [hcons, ← weilQuad_latticeTest hφ, latticeTest_refineVec φ h hk, weilQuad_latticeTest hφ,
    toeplitzForm_levinsonVec hκc hcoarse] at hle
  exact hle

/-- **Dyadic refinements are monotone** (under RH): `E_{2^{j+1}n}(φ, h/2^{j+1}) ≤ E_{2^jn}(φ, h/2^j)`. -/
theorem levinsonErr_dyadic_antitone (hRH : RiemannHypothesis) {φ : ℝ → ℝ} (hφ : φ ∈ realTests)
    (hφ0 : φ ≠ 0) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    Antitone fun j : ℕ => levinsonErr (weilSeq φ (h / 2 ^ j)) (2 ^ j * n) := by
  refine antitone_nat_of_succ_le fun j => ?_
  have hstep : h / 2 ^ (j + 1) = (h / 2 ^ j) / ((2 : ℕ) : ℝ) := by
    rw [pow_succ]; push_cast; ring
  have hsize : 2 ^ (j + 1) * n = 2 * (2 ^ j * n) := by ring
  have hpos : ∀ (s : ℝ), 0 < s → ∀ m, 0 < levinsonErr (weilSeq φ s) m := fun s hs m =>
    riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 s hs m
  rw [hstep, hsize]
  exact levinsonErr_refine_le hφ (h / 2 ^ j) two_pos
    (toeplitzPosDef_of_riemannHypothesis hRH hφ hφ0 (by positivity) _)
    fun m _ => (hpos _ (by positivity) m).ne'

/-- **The continuum margin** (under RH): along the dyadic refinements of a fixed total length the
lattice margins converge. -/
theorem tendsto_levinsonErr_dyadic (hRH : RiemannHypothesis) {φ : ℝ → ℝ} (hφ : φ ∈ realTests)
    (hφ0 : φ ≠ 0) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun j : ℕ => levinsonErr (weilSeq φ (h / 2 ^ j)) (2 ^ j * n))
      atTop (𝓝 L) := by
  have hanti := levinsonErr_dyadic_antitone hRH hφ hφ0 hh n
  have hbdd : BddBelow (Set.range fun j : ℕ => levinsonErr (weilSeq φ (h / 2 ^ j)) (2 ^ j * n)) :=
    ⟨0, by rintro _ ⟨j, rfl⟩; exact (riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 _
      (by positivity) _).le⟩
  refine ⟨_, ?_, tendsto_atTop_ciInf hanti hbdd⟩
  exact le_ciInf fun j => (riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 _
    (by positivity) _).le

end GaloisForLFunctions.GrowingWindowsOfSpecZ
