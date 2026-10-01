import GaloisForLFunctions.RHTower.SteinhausFullGaussianCompactModes
import GaloisForLFunctions.RHTower.RouteBFullSupport

open Filter Topology Finset Complex Set Metric
noncomputable section
namespace RHTower

/-- Exact finite prime-phase agreement preserves the entire normalized cofactor band. -/
theorem exists_relativeFullGaussianCofactor_compact_prefix_stability
    (b U : ℝ) (t : ℝ) (A : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b →
      ∀ R : ℝ, 1 ≤ R → R ≤ U → ∀ ω η : SteinhausModel.Omega,
        (∀ p ≤ B, ω p = η p) →
        ‖relativeFullGaussianCofactorScalarMode s t A R ω -
          relativeFullGaussianCofactorScalarMode s t A R η‖ < ε := by
  obtain ⟨B, _hB, δ, hδ, htol⟩ :=
    exists_relativeFullGaussianCofactor_compact_character_tolerance b U t A hε
  refine ⟨B, fun s hs0 hsb R hR hRU ω η hphase => ?_⟩
  apply htol s hs0 hsb R hR hRU η ω
  intro n hn
  have hX : SteinhausModel.X n ω = SteinhausModel.X n η := by
    apply X_congr_of_eqOn_primeFactors
    intro p hp
    exact hphase p ((Nat.le_of_dvd (by have := (mem_Icc.mp hn).1; omega)
      (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hn).2)
  rw [hX, sub_self, norm_zero]
  exact hδ

/-- One prescribed-prefix extension realizes every mode in a finite list on separated
scale blocks with arbitrary mean-weighted budgets and whole-disc accuracy. -/
theorem exists_prescribed_fullGaussianCofactor_compact_mode_blocks
    (S : Finset ℕ) (ω : SteinhausModel.Omega) (B : ℕ) (K ε : ℝ) (hε : 0 < ε)
    {c : ℂ} {r ρ : ℝ} (hρ : 0 < ρ) (hrρ : r < ρ)
    (hc0 : 0 < c.re - ρ) (hc1 : c.re + ρ < 1) :
    ∀ k : ℕ, ∀ t : Fin k → ℝ, ∃ ω' : SteinhausModel.Omega,
      (∀ p ∈ S, ω' p = ω p) ∧ ∃ M : Fin k → ℕ, ∃ A : Fin k → ℂ,
        (∀ i j, i < j → 2 * M i < M j) ∧
        ∀ i, B ≤ M i ∧ 1 ≤ M i ∧ A i ≠ 0 ∧ K ≤ (M i : ℝ) * ‖A i‖ ^ 2 ∧
          ∀ R : ℝ, (M i : ℝ) ≤ R → R ≤ 2 * (M i : ℝ) → ∀ s ∈ closedBall c r,
            ‖relativeFullGaussianCofactorScalarMode s (t i) (A i) R ω' -
              smoothAFEGaussianKernel (s + (t i : ℂ) * I)‖ < ε := by
  classical
  have hdisc (s : ℂ) (hs : s ∈ closedBall c r) : 0 ≤ s.re ∧ s.re ≤ c.re + ρ := by
    have habs : |s.re - c.re| ≤ dist s c := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
    have hd : dist s c ≤ r := hs
    have hl := (abs_le.mp habs).1
    have hu := (abs_le.mp habs).2
    constructor <;> linarith
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
      exists_relativeFullGaussianCofactor_compact_prefix_stability (c.re + ρ)
        (2 * (M i : ℝ)) (t i.castSucc) (A i) hhalf
    let S' := S ∪ univ.biUnion (fun i => range (C i + 1))
    let B' := B + (∑ i, 2 * M i) + 1
    obtain ⟨ω₁, hp₁, N, hN, hN1, a, ha, henergy, hmode⟩ :=
      exists_fullGaussianCofactor_compact_mode_block S' ω₀ (t (Fin.last k)) B' K
        (ε / 2) hhalf hρ hrρ hc0 hc1
    have hpreserve : ∀ i R, 1 ≤ R → R ≤ 2 * (M i : ℝ) → ∀ s ∈ closedBall c r,
        ‖relativeFullGaussianCofactorScalarMode s (t i.castSucc) (A i) R ω₁ -
          relativeFullGaussianCofactorScalarMode s (t i.castSucc) (A i) R ω₀‖ < ε / 2 := by
      intro i R hR hRU s hs
      apply hC i s (hdisc s hs).1 (hdisc s hs).2 R hR hRU ω₁ ω₀
      intro p hp
      apply hp₁ p
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨i, mem_univ _, mem_range.mpr (by omega)⟩)
    have hnewsep : ∀ i, 2 * M i < N := by
      intro i
      have hi : 2 * M i ≤ ∑ j, 2 * M j :=
        single_le_sum (f := fun j => 2 * M j)
          (fun j _ => show 0 ≤ 2 * M j from Nat.zero_le _) (mem_univ i)
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
        refine ⟨by omega, hN1, ha, henergy, fun R hR _ s hs => ?_⟩
        exact (hmode R hR s hs).trans (half_lt_self hε)
      · simp only [Fin.snoc_castSucc]
        refine ⟨(hblocks i').1, (hblocks i').2.1, (hblocks i').2.2.1,
          (hblocks i').2.2.2.1, ?_⟩
        intro R hlo hhi s hs
        have hR1 : 1 ≤ R := le_trans (by exact_mod_cast (hblocks i').2.1) hlo
        have hh := (hblocks i').2.2.2.2 R hlo hhi s hs
        simp only [Fin.init] at hh
        calc
          _ = ‖(relativeFullGaussianCofactorScalarMode s (t i'.castSucc) (A i') R ω₁ -
                relativeFullGaussianCofactorScalarMode s (t i'.castSucc) (A i') R ω₀) +
              (relativeFullGaussianCofactorScalarMode s (t i'.castSucc) (A i') R ω₀ -
                smoothAFEGaussianKernel (s + (t i'.castSucc : ℂ) * I))‖ := by
            congr 1
            ring
          _ ≤ ‖relativeFullGaussianCofactorScalarMode s (t i'.castSucc) (A i') R ω₁ -
                relativeFullGaussianCofactorScalarMode s (t i'.castSucc) (A i') R ω₀‖ +
              ‖relativeFullGaussianCofactorScalarMode s (t i'.castSucc) (A i') R ω₀ -
                smoothAFEGaussianKernel (s + (t i'.castSucc : ℂ) * I)‖ := norm_add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add (hpreserve i' R hR1 hhi s hs) hh
          _ = ε := by ring

end RHTower
