import GaloisForLFunctions.HTGeometry.SimpleSpectrumMatrixPerturbation

/-!
# Exact projective return is exactly rational gap rank one

A finite spectrum admits a positive time at which every anchored gap phase returns exactly if and
only if its anchored gap packet has rational rank at most one.  Clearing the finitely many
denominators produces the return time; conversely a return time places every gap in one cyclic
group of frequencies.

Consequently, from three levels onward every spectrum — and every Hermitian matrix — has both an
exactly returning and a never exactly returning simple neighbour, arbitrarily close.
-/

open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A positive time at which every anchored gap phase of a finite spectrum returns exactly. -/
def HasPositiveProjectiveReturn {d : ℕ} (E : Fin (d + 1) → ℝ) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∀ j : Fin d, ∃ m : ℤ, T * (E j.succ - E 0) = 2 * Real.pi * (m : ℝ)

/-- A finite rational family has a positive common denominator. -/
theorem exists_pos_nat_mul_isInt {d : ℕ} (q : Fin d → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ j, ∃ m : ℤ, (N : ℚ) * q j = (m : ℚ) := by
  classical
  refine ⟨∏ j, (q j).den, Finset.prod_pos fun j _ => (q j).pos, ?_⟩
  intro j
  obtain ⟨M, hM⟩ : ((q j).den : ℕ) ∣ ∏ i, (q i).den :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  refine ⟨(M : ℤ) * (q j).num, ?_⟩
  have hden : ((q j).den : ℚ) * q j = ((q j).num : ℚ) := by
    rw [mul_comm, Rat.mul_den_eq_num]
  rw [hM]
  push_cast
  rw [mul_comm ((q j).den : ℚ) (M : ℚ), mul_assoc, hden]

/-- **Exact projective return is rational gap rank at most one.** -/
theorem hasPositiveProjectiveReturn_iff_gapRank_le_one {d : ℕ} (E : Fin (d + 1) → ℝ) :
    HasPositiveProjectiveReturn E ↔
      rationalCoordinateRank (fun j : Fin d => E j.succ - E 0) ≤ 1 := by
  constructor
  · rintro ⟨T, hT, hm⟩
    choose m hmspec using hm
    have hTne : T ≠ 0 := ne_of_gt hT
    have ha : (2 * Real.pi / T) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi / T := by positivity
      exact ne_of_gt this
    have hle : Submodule.span ℚ (Set.range fun j : Fin d => E j.succ - E 0) ≤
        (ℚ ∙ (2 * Real.pi / T)) := by
      refine Submodule.span_le.2 ?_
      rintro z ⟨j, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨(m j : ℚ), ?_⟩
      rw [Rat.smul_def]
      have h := hmspec j
      push_cast
      field_simp
      linarith
    haveI : FiniteDimensional ℚ (ℚ ∙ (2 * Real.pi / T)) :=
      FiniteDimensional.span_singleton ℚ _
    calc rationalCoordinateRank (fun j : Fin d => E j.succ - E 0)
        ≤ Module.finrank ℚ (ℚ ∙ (2 * Real.pi / T)) := Submodule.finrank_mono hle
      _ = 1 := finrank_span_singleton ha
  · intro hrank
    by_cases hzero : ∀ j : Fin d, E j.succ - E 0 = 0
    · exact ⟨1, one_pos, fun j => ⟨0, by simp [hzero j]⟩⟩
    · push Not at hzero
      obtain ⟨j₀, hj₀⟩ := hzero
      haveI : FiniteDimensional ℚ
          (Submodule.span ℚ (Set.range fun j : Fin d => E j.succ - E 0)) :=
        FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
      have hspan : (ℚ ∙ (E j₀.succ - E 0)) =
          Submodule.span ℚ (Set.range fun j : Fin d => E j.succ - E 0) := by
        refine Submodule.eq_of_le_of_finrank_le ?_ ?_
        · rw [Submodule.span_singleton_le_iff_mem]
          exact Submodule.subset_span ⟨j₀, rfl⟩
        · rw [finrank_span_singleton hj₀]
          exact hrank
      have hcoeff : ∀ j : Fin d, ∃ q : ℚ, (q : ℝ) * (E j₀.succ - E 0) = E j.succ - E 0 := by
        intro j
        have hmem : (E j.succ - E 0) ∈ (ℚ ∙ (E j₀.succ - E 0)) := by
          rw [hspan]
          exact Submodule.subset_span ⟨j, rfl⟩
        obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp hmem
        exact ⟨q, by rwa [Rat.smul_def] at hq⟩
      choose q hq using hcoeff
      obtain ⟨N, hN, hNint⟩ := exists_pos_nat_mul_isInt q
      choose mm hmm using hNint
      have hNreal : ∀ j : Fin d, (N : ℝ) * (q j : ℝ) = (mm j : ℝ) := by
        intro j
        exact_mod_cast congrArg (fun r : ℚ => (r : ℝ)) (hmm j)
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      rcases lt_or_gt_of_ne hj₀ with hneg | hpos
      · refine ⟨-(2 * Real.pi * N / (E j₀.succ - E 0)), ?_, ?_⟩
        · have : 2 * Real.pi * (N : ℝ) / (E j₀.succ - E 0) < 0 :=
            div_neg_of_pos_of_neg (by positivity) hneg
          linarith
        · intro j
          refine ⟨-(mm j), ?_⟩
          have hstep : -(2 * Real.pi * (N : ℝ) / (E j₀.succ - E 0)) * (E j.succ - E 0)
              = -(2 * Real.pi * ((N : ℝ) * (q j : ℝ))) := by
            rw [← hq j]
            field_simp [hj₀]
          rw [hstep, hNreal j]
          push_cast
          ring
      · refine ⟨2 * Real.pi * N / (E j₀.succ - E 0), ?_, ?_⟩
        · exact div_pos (by positivity) hpos
        · intro j
          refine ⟨mm j, ?_⟩
          have hstep : (2 * Real.pi * (N : ℝ) / (E j₀.succ - E 0)) * (E j.succ - E 0)
              = 2 * Real.pi * ((N : ℝ) * (q j : ℝ)) := by
            rw [← hq j]
            field_simp [hj₀]
          rw [hstep, hNreal j]

/-- Exactly returning simple spectra are dense. -/
theorem exists_close_simpleSpectrum_hasPositiveProjectiveReturn {d : ℕ} (hd : 0 < d)
    (E : Fin (d + 1) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ E' : Fin (d + 1) → ℝ, Function.Injective E' ∧ (∀ i, dist (E' i) (E i) < ε) ∧
      HasPositiveProjectiveReturn E' := by
  obtain ⟨E', hinj, hclose, hrank⟩ :=
    exists_simpleSpectrum_close_gapRank (k := 1) one_pos hd E hε
  exact ⟨E', hinj, hclose,
    (hasPositiveProjectiveReturn_iff_gapRank_le_one E').mpr (le_of_eq hrank)⟩

/-- From three levels onward, simple spectra with no positive exact projective return are
dense. -/
theorem exists_close_simpleSpectrum_not_hasPositiveProjectiveReturn {d : ℕ} (hd : 2 ≤ d)
    (E : Fin (d + 1) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ E' : Fin (d + 1) → ℝ, Function.Injective E' ∧ (∀ i, dist (E' i) (E i) < ε) ∧
      ¬ HasPositiveProjectiveReturn E' := by
  obtain ⟨E', hinj, hclose, hrank⟩ :=
    exists_simpleSpectrum_close_gapRank (k := 2) two_pos hd E hε
  refine ⟨E', hinj, hclose, ?_⟩
  intro hret
  have := (hasPositiveProjectiveReturn_iff_gapRank_le_one E').mp hret
  omega

/-- **Exact repetition and exact nonrepetition are both dense.**  From three levels onward every
spectrum has, inside every tolerance, a simple exactly returning neighbour and a simple neighbour
with no positive exact projective return. -/
theorem exists_close_simpleSpectrum_periodic_and_aperiodic {d : ℕ} (hd : 2 ≤ d)
    (E : Fin (d + 1) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∃ E' : Fin (d + 1) → ℝ, Function.Injective E' ∧ (∀ i, dist (E' i) (E i) < ε) ∧
        HasPositiveProjectiveReturn E') ∧
      ∃ E' : Fin (d + 1) → ℝ, Function.Injective E' ∧ (∀ i, dist (E' i) (E i) < ε) ∧
        ¬ HasPositiveProjectiveReturn E' :=
  ⟨exists_close_simpleSpectrum_hasPositiveProjectiveReturn (by omega) E hε,
    exists_close_simpleSpectrum_not_hasPositiveProjectiveReturn hd E hε⟩

/-- **Every Hamiltonian neighbourhood contains both eternities.**  From three levels onward every
Hermitian matrix has, in every operator-norm neighbourhood, a commuting simple-spectrum Hermitian
matrix which returns exactly and one which never returns exactly. -/
theorem exists_isHermitian_commuting_close_periodic_and_aperiodic {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    (∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ),
        B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧ ‖B - A‖ < ε ∧
          B = (Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
                hA.eigenvectorUnitary) (Matrix.diagonal (RCLike.ofReal ∘ E')) ∧
          HasPositiveProjectiveReturn E') ∧
      ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ),
        B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧ ‖B - A‖ < ε ∧
          B = (Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
                hA.eigenvectorUnitary) (Matrix.diagonal (RCLike.ofReal ∘ E')) ∧
          ¬ HasPositiveProjectiveReturn E' := by
  constructor
  · obtain ⟨B, E', hherm, hcomm, hinj, hnorm, hconj, hrank⟩ :=
      exists_isHermitian_commuting_close_gapRank (k := 1) one_pos (by omega) A hA hε
    exact ⟨B, E', hherm, hcomm, hinj, hnorm, hconj,
      (hasPositiveProjectiveReturn_iff_gapRank_le_one E').mpr (le_of_eq hrank)⟩
  · obtain ⟨B, E', hherm, hcomm, hinj, hnorm, hconj, hrank⟩ :=
      exists_isHermitian_commuting_close_gapRank (k := 2) two_pos hn A hA hε
    refine ⟨B, E', hherm, hcomm, hinj, hnorm, hconj, ?_⟩
    intro hret
    have := (hasPositiveProjectiveReturn_iff_gapRank_le_one E').mp hret
    omega

/-- A nonzero coordinate forces positive rational rank. -/
theorem rationalCoordinateRank_pos {n : ℕ} {ω : Fin n → ℝ} {i : Fin n} (h : ω i ≠ 0) :
    0 < rationalCoordinateRank ω := by
  haveI : Module.Finite ℚ (Submodule.span ℚ (Set.range ω)) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range ω)
  have hmem : ω i ∈ Submodule.span ℚ (Set.range ω) := Submodule.subset_span ⟨i, rfl⟩
  have hnt : Nontrivial (Submodule.span ℚ (Set.range ω)) := by
    refine ⟨⟨0, ⟨ω i, hmem⟩, ?_⟩⟩
    simp [Subtype.ext_iff, h, eq_comm]
  exact Module.finrank_pos

/-- **Corollary 1 for a simple spectrum.**  A simple finite spectrum has a positive exact global
projective return exactly when its gap rank is one: simplicity rules out rank zero, because the
first gap is already nonzero. -/
theorem hasPositiveProjectiveReturn_iff_gapRank_eq_one {d : ℕ} (hd : 0 < d)
    {E : Fin (d + 1) → ℝ} (hinj : Function.Injective E) :
    HasPositiveProjectiveReturn E ↔
      rationalCoordinateRank (fun j : Fin d => E j.succ - E 0) = 1 := by
  have hzero : (⟨0, hd⟩ : Fin d).succ ≠ 0 := Fin.succ_ne_zero _
  have hne : E (⟨0, hd⟩ : Fin d).succ - E 0 ≠ 0 := by
    intro hcon
    exact hzero (hinj (sub_eq_zero.mp hcon))
  have hpos : 0 < rationalCoordinateRank (fun j : Fin d => E j.succ - E 0) :=
    rationalCoordinateRank_pos (i := (⟨0, hd⟩ : Fin d)) hne
  constructor
  · intro hret
    have hle := (hasPositiveProjectiveReturn_iff_gapRank_le_one E).mp hret
    omega
  · intro hrank
    exact (hasPositiveProjectiveReturn_iff_gapRank_le_one E).mpr (le_of_eq hrank)

end

end GaloisForLFunctions.HTGeometry
