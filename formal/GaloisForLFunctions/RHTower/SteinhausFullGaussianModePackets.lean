import GaloisForLFunctions.RHTower.SteinhausFullGaussianCofactorModes


open Filter Topology Finset
noncomputable section
namespace RHTower

/-- One extension of any prescribed finite phase assignment realizes a finite list of Gaussian
Mellin modes on separated scale blocks. Tail preservation keeps all previously placed modes. -/
theorem exists_prescribed_fullGaussianCofactor_mode_blocks
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (ω : SteinhausModel.Omega) (B : ℕ) (K ε : ℝ) (hε : 0 < ε) :
    ∀ k : ℕ, ∀ t : Fin k → ℝ, ∃ ω' : SteinhausModel.Omega,
      (∀ p ∈ S, ω' p = ω p) ∧ ∃ M : Fin k → ℕ, ∃ A : Fin k → ℂ,
        (∀ i j, i < j → 2 * M i < M j) ∧
        ∀ i, B ≤ M i ∧ 1 ≤ M i ∧ A i ≠ 0 ∧ K ≤ (M i : ℝ) * ‖A i‖ ^ 2 ∧
          ∀ R : ℝ, (M i : ℝ) ≤ R → R ≤ 2 * (M i : ℝ) →
            ‖relativeFullGaussianCofactorMode s (t i) (A i) R ω' -
              (fun j => smoothAFEGaussianKernel (s j + (t i : ℂ) * Complex.I))‖ < ε := by
  classical
  intro k
  induction k generalizing ε with
  | zero =>
    intro t
    exact ⟨ω, fun _ _ => rfl, Fin.elim0, Fin.elim0,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro t
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨ω₀, hp₀, M, A, hsep, hblocks⟩ := ih (ε / 2) hhalf (Fin.init t)
    choose C hC using fun i =>
      exists_relativeFullGaussianCofactorMode_prefix_stability s (fun j => (hs j).le)
        (t i.castSucc) ((hblocks i).2.2.1) (2 * (M i : ℝ)) hhalf
    let S' := S ∪ univ.biUnion (fun i => range (C i + 1))
    let B' := B + (∑ i, 2 * M i) + 1
    obtain ⟨ω₁, hp₁, N, hN, hN1, a, ha, henergy, hmode⟩ :=
      exists_fullGaussianCofactor_mode_block s hs hs1 S' ω₀ (t (Fin.last k)) B' K
        (ε / 2) hhalf
    have hpreserve : ∀ i R, 1 ≤ R → R ≤ 2 * (M i : ℝ) →
        ‖relativeFullGaussianCofactorMode s (t i.castSucc) (A i) R ω₁ -
          relativeFullGaussianCofactorMode s (t i.castSucc) (A i) R ω₀‖ < ε / 2 := by
      intro i R hR hRU
      apply hC i R hR hRU ω₁ ω₀
      intro p hp
      apply hp₁ p
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨i, mem_univ _, mem_range.mpr (by omega)⟩)
    have hnewsep : ∀ i, 2 * M i < N := by
      intro i
      have hi : 2 * M i ≤ ∑ j, 2 * M j :=
        single_le_sum (fun j _ => show 0 ≤ 2 * M j from Nat.zero_le _) (mem_univ i)
      omega
    refine ⟨ω₁, ?_, Fin.snoc M N, Fin.snoc A a, ?_, ?_⟩
    · intro p hp
      exact (hp₁ p (mem_union_left _ hp)).trans (hp₀ p hp)
    · intro i j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · refine Fin.lastCases ?_ (fun i' => ?_) i
        · simp
        · intro _
          simpa using hnewsep i'
      · refine Fin.lastCases ?_ (fun i' => ?_) i
        · intro hij
          have hj := j'.isLt
          change k < j'.val at hij
          omega
        · intro hij
          simpa using hsep i' j' (by simpa using hij)
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp only [Fin.snoc_last]
        refine ⟨by omega, hN1, ha, henergy, fun R hR _ => ?_⟩
        exact (hmode R hR).trans (half_lt_self hε)
      · simp only [Fin.snoc_castSucc]
        refine ⟨(hblocks i').1, (hblocks i').2.1, (hblocks i').2.2.1,
          (hblocks i').2.2.2.1, ?_⟩
        intro R hlo hhi
        have hR1 : 1 ≤ R := le_trans (by exact_mod_cast (hblocks i').2.1) hlo
        have hh := (hblocks i').2.2.2.2 R hlo hhi
        simp only [Fin.init] at hh
        calc
          _ = ‖(relativeFullGaussianCofactorMode s (t i'.castSucc) (A i') R ω₁ -
                relativeFullGaussianCofactorMode s (t i'.castSucc) (A i') R ω₀) +
              (relativeFullGaussianCofactorMode s (t i'.castSucc) (A i') R ω₀ -
                (fun j => smoothAFEGaussianKernel (s j + (t i'.castSucc : ℂ) * Complex.I)))‖ := by
            congr 1
            abel
          _ ≤ ‖relativeFullGaussianCofactorMode s (t i'.castSucc) (A i') R ω₁ -
                relativeFullGaussianCofactorMode s (t i'.castSucc) (A i') R ω₀‖ +
              ‖relativeFullGaussianCofactorMode s (t i'.castSucc) (A i') R ω₀ -
                (fun j => smoothAFEGaussianKernel (s j + (t i'.castSucc : ℂ) * Complex.I))‖ :=
            norm_add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add (hpreserve i' R hR1 hhi) hh
          _ = ε := by ring

end RHTower
