import GaloisForLFunctions.HTGeometry.CommutingTermTemporalRankBound
import GaloisForLFunctions.HTGeometry.KroneckerSumSpectrum
import Mathlib

/-!
# Every eigenvalue of a commuting Hermitian sum splits

For pairwise commuting Hermitian matrices, each eigenvalue of the sum is a sum of eigenvalues of
the summands.  The proof needs no simultaneous eigenbasis: in the eigenbasis of one summand the
other is block diagonal across equal eigenvalues, so restricting an eigenvector of the sum to one
eigenvalue block of the first summand produces a joint eigenvector of both.

Consequently a Hamiltonian written as `m` commuting terms with at most four levels each — for
instance two-qubit terms — has anchored temporal rank at most `3 m`, linear rather than
exponential in the number of sites.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonzero eigenvector exhibits its eigenvalue in the Hermitian eigenvalue list. -/
theorem exists_eigenvalues_eq_of_mulVec {B : Matrix n n ℂ} (hB : B.IsHermitian)
    {mu : ℝ} {w : n → ℂ} (hw : w ≠ 0) (hBw : B *ᵥ w = (mu : ℂ) • w) :
    ∃ i, hB.eigenvalues i = mu := by
  classical
  set V : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ) with hV
  have hVstar : star V * V = 1 := UnitaryGroup.star_mul_self _
  have hVmul : V * star V = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := (hB.eigenvectorUnitary : Matrix n n ℂ))).mp
      (hB.eigenvectorUnitary).2
    simp [hV]
  set x : n → ℂ := star V *ᵥ w with hx
  have hxne : x ≠ 0 := by
    intro hzero
    apply hw
    have : V *ᵥ x = w := by
      rw [hx, Matrix.mulVec_mulVec, hVmul, Matrix.one_mulVec]
    rw [hzero, Matrix.mulVec_zero] at this
    exact this.symm
  have hspec : B = V * Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) * star V :=
    hB.spectral_theorem
  have hconj : star V * B * V = Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
    conv_lhs => rw [hspec]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hVstar, Matrix.one_mul,
      Matrix.mul_assoc, hVstar, Matrix.mul_one]
  have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) *ᵥ x = (mu : ℂ) • x := by
    have hwx : V *ᵥ x = w := by
      rw [hx, Matrix.mulVec_mulVec, hVmul, Matrix.one_mulVec]
    calc Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) *ᵥ x
        = (star V * B * V) *ᵥ x := by rw [hconj]
      _ = star V *ᵥ (B *ᵥ (V *ᵥ x)) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = star V *ᵥ (B *ᵥ w) := by rw [hwx]
      _ = (mu : ℂ) • x := by rw [hBw, Matrix.mulVec_smul, hx]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    exact hxne (funext fun i => not_not.mp (fun h => hcon ⟨i, h⟩))
  refine ⟨i, ?_⟩
  have := congrFun hdiag i
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at this
  have hcast : ((hB.eigenvalues i : ℝ) : ℂ) = ((mu : ℝ) : ℂ) := by
    have hfac : (((hB.eigenvalues i : ℝ) : ℂ) - ((mu : ℝ) : ℂ)) * x i = 0 := by
      rw [sub_mul]; linear_combination this
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hi
  exact_mod_cast hcast

/-- **Commuting Hermitian eigenvalue splitting.**  For a commuting Hermitian pair, every
eigenvector of the sum yields a joint eigenvector, so the eigenvalue splits. -/
theorem exists_joint_eigenvector_of_commute
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hcomm : A * B = B * A)
    {E : ℝ} {v : n → ℂ} (hv : v ≠ 0) (hEv : (A + B) *ᵥ v = (E : ℂ) • v) :
    ∃ (lam : ℝ) (w : n → ℂ), w ≠ 0 ∧ (∃ i, hA.eigenvalues i = lam) ∧
      A *ᵥ w = (lam : ℂ) • w ∧ B *ᵥ w = ((E - lam : ℝ) : ℂ) • w := by
  classical
  set V : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hV
  have hVstar : star V * V = 1 := UnitaryGroup.star_mul_self _
  have hVmul : V * star V = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := (hA.eigenvectorUnitary : Matrix n n ℂ))).mp
      (hA.eigenvectorUnitary).2
    simp [hV]
  set eig : n → ℝ := hA.eigenvalues with heig
  set C : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ eig) with hC
  set D : Matrix n n ℂ := star V * B * V with hD
  have hspec : A = V * C * star V := hA.spectral_theorem
  -- the conjugated pair still commutes
  have hCD : C * D = D * C := by
    have hAV : star V * A * V = C := by
      conv_lhs => rw [hspec]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hVstar, Matrix.one_mul,
        Matrix.mul_assoc, hVstar, Matrix.mul_one]
    calc C * D = (star V * A * V) * (star V * B * V) := by rw [hAV]
      _ = star V * A * (V * star V) * B * V := by noncomm_ring
      _ = star V * (A * B) * V := by rw [hVmul]; noncomm_ring
      _ = star V * (B * A) * V := by rw [hcomm]
      _ = star V * B * (V * star V) * A * V := by rw [hVmul]; noncomm_ring
      _ = (star V * B * V) * (star V * A * V) := by noncomm_ring
      _ = D * C := by rw [hAV]
  have hblock : ∀ i j, eig i ≠ eig j → D i j = 0 := by
    intro i j hij
    have hcd := congrFun (congrFun hCD i) j
    simp only [hC, Matrix.diagonal_mul, Matrix.mul_diagonal, Function.comp_apply] at hcd
    have hne : ((eig i : ℝ) : ℂ) - ((eig j : ℝ) : ℂ) ≠ 0 := by
      simp only [sub_ne_zero]
      exact_mod_cast hij
    have : (((eig i : ℝ) : ℂ) - ((eig j : ℝ) : ℂ)) * D i j = 0 := by
      rw [sub_mul]; linear_combination hcd
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · exact h
  -- transport the eigenvector
  set x : n → ℂ := star V *ᵥ v with hx
  have hxv : V *ᵥ x = v := by rw [hx, Matrix.mulVec_mulVec, hVmul, Matrix.one_mulVec]
  have hxne : x ≠ 0 := by
    intro hzero
    apply hv
    rw [← hxv, hzero, Matrix.mulVec_zero]
  have hCDx : (C + D) *ᵥ x = (E : ℂ) • x := by
    have hconj : star V * (A + B) * V = C + D := by
      have hAV : star V * A * V = C := by
        conv_lhs => rw [hspec]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hVstar, Matrix.one_mul,
          Matrix.mul_assoc, hVstar, Matrix.mul_one]
      have hexp : star V * (A + B) * V = star V * A * V + star V * B * V := by
        noncomm_ring
      rw [hexp, hAV, hD]
    have hstep : star V *ᵥ ((A + B) *ᵥ v) = (E : ℂ) • x := by
      rw [hEv, Matrix.mulVec_smul, hx]
    rw [← hconj]
    calc (star V * (A + B) * V) *ᵥ x
        = star V *ᵥ ((A + B) *ᵥ (V *ᵥ x)) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = star V *ᵥ ((A + B) *ᵥ v) := by rw [hxv]
      _ = (E : ℂ) • x := hstep
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    exact hxne (funext fun i => not_not.mp (fun h => hcon ⟨i, h⟩))
  set lam : ℝ := eig i0 with hlam
  set y : n → ℂ := fun i => if eig i = lam then x i else 0 with hy
  have hyne : y ≠ 0 := by
    intro hzero
    apply hi0
    have := congrFun hzero i0
    simpa [hy, hlam] using this
  have hCy : C *ᵥ y = (lam : ℂ) • y := by
    funext i
    simp only [hC, Matrix.mulVec_diagonal, Function.comp_apply, Pi.smul_apply, smul_eq_mul, hy]
    by_cases hi : eig i = lam
    · simp [hi]
    · simp [hi]
  have hDy : D *ᵥ y = ((E - lam : ℝ) : ℂ) • y := by
    funext i
    have hsum : (D *ᵥ y) i = ∑ j, D i j * y j := rfl
    by_cases hi : eig i = lam
    · have hDx : (D *ᵥ y) i = (D *ᵥ x) i := by
        rw [hsum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : eig j = lam
        · simp [hy, hj]
        · have : D i j = 0 := hblock i j (by rw [hi]; exact fun hcon => hj hcon.symm)
          simp [hy, hj, this]
      have hCx := congrFun hCDx i
      simp only [Matrix.add_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hCx
      have hCxi : (C *ᵥ x) i = ((eig i : ℝ) : ℂ) * x i := by
        simp [hC, Matrix.mulVec_diagonal]
      rw [hCxi, hi] at hCx
      have hyi : y i = x i := by simp [hy, hi]
      have hDxi : (D *ᵥ x) i = (E : ℂ) * x i - ((lam : ℝ) : ℂ) * x i := by
        linear_combination hCx
      rw [hDx, hDxi]
      simp only [Pi.smul_apply, smul_eq_mul, hyi]
      push_cast
      ring
    · have hzero : (D *ᵥ y) i = 0 := by
        rw [hsum]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : eig j = lam
        · have : D i j = 0 := hblock i j (by rw [hj]; exact hi)
          simp [this]
        · simp [hy, hj]
      have hyi : y i = 0 := by simp [hy, hi]
      rw [hzero]
      simp only [Pi.smul_apply, smul_eq_mul, hyi, mul_zero]
  refine ⟨lam, V *ᵥ y, ?_, ⟨i0, rfl⟩, ?_, ?_⟩
  · intro hcon
    apply hyne
    have : star V *ᵥ (V *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, hVstar, Matrix.one_mulVec]
    rw [hcon, Matrix.mulVec_zero] at this
    exact this.symm
  · calc A *ᵥ (V *ᵥ y) = (V * C * star V * V) *ᵥ y := by
          rw [hspec]; simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (V * C) *ᵥ y := by rw [Matrix.mul_assoc, hVstar, Matrix.mul_one]
      _ = V *ᵥ (C *ᵥ y) := by rw [Matrix.mulVec_mulVec]
      _ = (lam : ℂ) • (V *ᵥ y) := by rw [hCy, Matrix.mulVec_smul]
  · calc B *ᵥ (V *ᵥ y) = (B * V) *ᵥ y := by rw [Matrix.mulVec_mulVec]
      _ = (V * (star V * B * V)) *ᵥ y := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hVmul, Matrix.one_mul]
      _ = V *ᵥ (D *ᵥ y) := by rw [← hD, Matrix.mulVec_mulVec]
      _ = ((E - lam : ℝ) : ℂ) • (V *ᵥ y) := by rw [hDy, Matrix.mulVec_smul]


/-- **Commuting Hermitian spectral splitting.**  Every eigenvalue of a finite sum of pairwise
commuting Hermitian matrices is a sum of eigenvalues of the summands. -/
theorem exists_eigenvalue_split_of_commuting
    {K : Type*} [DecidableEq K] (h : K → Matrix n n ℂ)
    (hherm : ∀ k, (h k).IsHermitian)
    (hcomm : ∀ k l, h k * h l = h l * h k) (s : Finset K) :
    ∀ {E : ℝ} {v : n → ℂ}, v ≠ 0 → (∑ k ∈ s, h k) *ᵥ v = (E : ℂ) • v →
      ∃ lam : K → ℝ, (∀ k ∈ s, ∃ i, (hherm k).eigenvalues i = lam k) ∧
        E = ∑ k ∈ s, lam k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro E v hv hEv
      refine ⟨fun _ => 0, by simp, ?_⟩
      simp only [Finset.sum_empty] at hEv ⊢
      have : ((E : ℂ)) • v = 0 := by
        rw [← hEv]; simp
      rcases smul_eq_zero.mp this with hE | hvz
      · exact_mod_cast hE
      · exact absurd hvz hv
  | insert a t ha ih =>
      intro E v hv hEv
      have hsplit : (∑ k ∈ insert a t, h k) = h a + ∑ k ∈ t, h k :=
        Finset.sum_insert ha
      have hcommAB : h a * (∑ k ∈ t, h k) = (∑ k ∈ t, h k) * h a := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => hcomm a k
      rw [hsplit] at hEv
      obtain ⟨lamA, w, hw, ⟨i, hi⟩, -, hBw⟩ :=
        exists_joint_eigenvector_of_commute (hherm a) hcommAB hv hEv
      obtain ⟨lam', hlam', hsum'⟩ := ih hw hBw
      refine ⟨Function.update lam' a lamA, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hkt
        · exact ⟨i, by rw [Function.update_self]; exact hi⟩
        · obtain ⟨j, hj⟩ := hlam' k hkt
          refine ⟨j, ?_⟩
          rw [Function.update_of_ne (by rintro rfl; exact ha hkt)]
          exact hj
      · rw [Finset.sum_insert ha, Function.update_self]
        have hrest : ∑ k ∈ t, Function.update lam' a lamA k = ∑ k ∈ t, lam' k := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Function.update_of_ne (by rintro rfl; exact ha hk)]
        rw [hrest]
        linarith [hsum']

/-- Every Hermitian eigenvalue is realised by a nonzero eigenvector. -/
theorem exists_ne_zero_mulVec_eigenvalues {H : Matrix n n ℂ} (hH : H.IsHermitian) (i : n) :
    ∃ v : n → ℂ, v ≠ 0 ∧ H *ᵥ v = ((hH.eigenvalues i : ℝ) : ℂ) • v := by
  classical
  set V : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hV
  have hVstar : star V * V = 1 := UnitaryGroup.star_mul_self _
  have hspec : H = V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star V :=
    hH.spectral_theorem
  have hVmul : V * star V = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := (hH.eigenvectorUnitary : Matrix n n ℂ))).mp
      (hH.eigenvectorUnitary).2
    simp [hV]
  refine ⟨V *ᵥ (Pi.single i 1 : n → ℂ), ?_, ?_⟩
  · intro hzero
    have hback : star V *ᵥ (V *ᵥ ((Pi.single i 1 : n → ℂ))) = (Pi.single i 1 : n → ℂ) := by
      rw [Matrix.mulVec_mulVec, hVstar, Matrix.one_mulVec]
    rw [hzero, Matrix.mulVec_zero] at hback
    have h1 : ((Pi.single i 1 : n → ℂ)) i = 0 := by rw [← hback]; rfl
    rw [Pi.single_eq_same] at h1
    exact one_ne_zero h1
  · have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ ((Pi.single i 1 : n → ℂ)) =
        ((hH.eigenvalues i : ℝ) : ℂ) • (Pi.single i 1 : n → ℂ) := by
      funext j
      simp only [Matrix.mulVec_diagonal, Function.comp_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply]
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    have hHV : H * V = V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
      conv_lhs => rw [hspec]
      rw [Matrix.mul_assoc, hVstar, Matrix.mul_one]
    calc H *ᵥ (V *ᵥ (Pi.single i 1 : n → ℂ))
        = (H * V) *ᵥ (Pi.single i 1 : n → ℂ) := by rw [Matrix.mulVec_mulVec]
      _ = (V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) *ᵥ (Pi.single i 1 : n → ℂ) := by
          rw [hHV]
      _ = V *ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (Pi.single i 1 : n → ℂ)) := by
          rw [Matrix.mulVec_mulVec]
      _ = ((hH.eigenvalues i : ℝ) : ℂ) • (V *ᵥ (Pi.single i 1 : n → ℂ)) := by
          rw [hdiag, Matrix.mulVec_smul]

set_option maxHeartbeats 1000000 in
/-- **Commuting-term temporal-rank law.**  A Hamiltonian written as a finite family of pairwise
commuting Hermitian terms, each with at most `v` distinct levels, has anchored temporal rank at
most `|K| (v - 1)`.  For two-qubit terms `v = 4`, giving the linear bound `3 |K|`. -/
theorem anchoredTemporalRank_le_of_commuting
    {K : Type*} [Fintype K] [DecidableEq K] (h : K → Matrix n n ℂ)
    (hherm : ∀ k, (h k).IsHermitian)
    (hcomm : ∀ k l, h k * h l = h l * h k)
    (hH : (∑ k, h k).IsHermitian) (r : n) {v : ℕ}
    (hcard : ∀ k, (Finset.univ.image (hherm k).eigenvalues).card ≤ v) :
    anchoredTemporalRank hH.eigenvalues r ≤ Fintype.card K * (v - 1) := by
  have hchoice : ∀ i : n, ∃ lam : K → ℝ,
      (∀ k, ∃ j, (hherm k).eigenvalues j = lam k) ∧ hH.eigenvalues i = ∑ k : K, lam k := by
    intro i
    obtain ⟨w, hw, hHw⟩ := exists_ne_zero_mulVec_eigenvalues hH i
    obtain ⟨lam, hlam, hsum⟩ :=
      exists_eigenvalue_split_of_commuting h hherm hcomm Finset.univ hw hHw
    exact ⟨lam, fun k => hlam k (Finset.mem_univ k), hsum⟩
  choose lam hlam hsum using hchoice
  have hcard' : ∀ k, (Finset.univ.image fun i : n => lam i k).card ≤ v := by
    intro k
    refine le_trans (Finset.card_le_card ?_) (hcard k)
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, hj⟩ := hlam i k
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
  have hHeq : hH.eigenvalues = fun i => ∑ k : K, lam i k := funext hsum
  rw [hHeq]
  exact anchoredTemporalRank_sum_le (fun (k : K) (i : n) => lam i k) r hcard'


/-! ## Terms supported on a tensor factor -/

section Support

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty J]

/-- The zero matrix has vanishing Hermitian eigenvalue list. -/
theorem eigenvalues_zero_eq_zero :
    (Matrix.isHermitian_zero (n := J) (α := ℂ)).eigenvalues = 0 := by
  funext j
  have hrange : Set.range (Matrix.isHermitian_zero (n := J) (α := ℂ)).eigenvalues =
      spectrum ℝ (0 : Matrix J J ℂ) :=
    (Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues
      (𝕜 := ℂ) (Matrix.isHermitian_zero (n := J) (α := ℂ))).symm
  have hmem : (Matrix.isHermitian_zero (n := J) (α := ℂ)).eigenvalues j ∈
      spectrum ℝ (0 : Matrix J J ℂ) := by
    rw [← hrange]
    exact ⟨j, rfl⟩
  rw [spectrum.zero_eq] at hmem
  simpa using hmem

/-- Adjoining an identity tensor factor does not enlarge the eigenvalue value set: a term
supported on a tensor factor has at most as many distinct levels as on that factor alone. -/
theorem card_image_eigenvalues_kroneckerSum_zero
    {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (Finset.univ.image
        (isHermitian_kroneckerSum hX (Matrix.isHermitian_zero (n := J) (α := ℂ))).eigenvalues).card
      = (Finset.univ.image hX.eigenvalues).card := by
  classical
  have hrange := range_eigenvalues_kroneckerSum hX
    (Matrix.isHermitian_zero (n := J) (α := ℂ))
  rw [eigenvalues_zero_eq_zero] at hrange
  have hsimpl : Set.range (fun p : I × J => hX.eigenvalues p.1 + (0 : J → ℝ) p.2) =
      Set.range hX.eigenvalues := by
    ext r
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, by simp⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j⟩ := ‹Nonempty J›
      exact ⟨(i, j), by simp⟩
  rw [hsimpl] at hrange
  congr 1
  ext r
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, rfl⟩
    have hmem : (isHermitian_kroneckerSum hX
        (Matrix.isHermitian_zero (n := J) (α := ℂ))).eigenvalues p ∈
        Set.range hX.eigenvalues := by
      rw [← hrange]; exact ⟨p, rfl⟩
    exact hmem
  · rintro ⟨i, rfl⟩
    have hmem : hX.eigenvalues i ∈ Set.range (isHermitian_kroneckerSum hX
        (Matrix.isHermitian_zero (n := J) (α := ℂ))).eigenvalues := by
      rw [hrange]; exact ⟨i, rfl⟩
    exact hmem

end Support

end

end GaloisForLFunctions.HTGeometry
