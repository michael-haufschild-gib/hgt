import GaloisForLFunctions.HTGeometry.ArithmeticTemporalRankInstability

/-!
# Simple spectra of prescribed temporal dimension

Every finite real spectrum has arbitrarily close spectra which are simple — all levels distinct —
and whose gap packet has any prescribed positive rational rank not exceeding the number of gaps.

The construction perturbs the gaps to a rationally independent family in the first `k` slots and to
rational multiples of the first slot in the remaining ones; the rational multipliers are chosen
distinct and different from `0` and `1`, which is exactly what keeps all levels apart.
-/

open Filter Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rational multiples of a nonzero real approximate every real while avoiding any prescribed
finite set of multipliers. -/
theorem exists_rat_mul_close_notMem {b : ℝ} (hb : b ≠ 0) {ε : ℝ} (hε : 0 < ε) (x : ℝ)
    (s : Finset ℚ) : ∃ q : ℚ, q ∉ s ∧ dist ((q : ℝ) * b) x < ε := by
  have habs : 0 < |b| := abs_pos.mpr hb
  set c : ℝ := x / b with hc
  set δ : ℝ := ε / |b| with hδdef
  have hδ : 0 < δ := div_pos hε habs
  obtain ⟨a₁, ha₁l, ha₁r⟩ := exists_rat_btwn (show c - δ < c by linarith)
  obtain ⟨a₂, ha₂l, ha₂r⟩ := exists_rat_btwn (show c < c + δ by linarith)
  have hlt : a₁ < a₂ := by exact_mod_cast lt_trans ha₁r ha₂l
  have hinf : (Set.Ioo a₁ a₂).Infinite := Set.infinite_coe_iff.mp (Set.Ioo.infinite hlt)
  obtain ⟨q, hq, hqs⟩ := hinf.exists_notMem_finset s
  refine ⟨q, hqs, ?_⟩
  have hq1 : (a₁ : ℝ) < (q : ℝ) := by exact_mod_cast hq.1
  have hq2 : ((q : ℝ)) < (a₂ : ℝ) := by exact_mod_cast hq.2
  have hqc : |(q : ℝ) - c| < δ := by
    rw [abs_lt]
    constructor <;> linarith
  have hbc : b * c = x := by
    rw [hc]
    field_simp
  have hdist : dist ((q : ℝ) * b) x = |b| * |(q : ℝ) - c| := by
    rw [Real.dist_eq, ← abs_mul, ← hbc]
    congr 1
    ring
  rw [hdist]
  calc |b| * |(q : ℝ) - c| < |b| * δ := mul_lt_mul_of_pos_left hqc habs
    _ = ε := by
        rw [hδdef]
        field_simp

/-- A property of rationals which can always be satisfied outside any finite set can be satisfied
by an injective family. -/
theorem exists_injective_rat_choice : ∀ {r : ℕ} (P : Fin r → ℚ → Prop),
    (∀ (j : Fin r) (s : Finset ℚ), ∃ q, q ∉ s ∧ P j q) →
    ∃ q : Fin r → ℚ, Function.Injective q ∧ ∀ j, P j (q j) := by
  intro r
  induction r with
  | zero =>
    intro P _
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun j => Fin.elim0 j⟩
  | succ r ih =>
    intro P hP
    classical
    obtain ⟨q', hq'inj, hq'⟩ := ih (fun j => P j.castSucc) fun j s => hP j.castSucc s
    obtain ⟨qlast, hqlast, hPlast⟩ := hP (Fin.last r) (Finset.image q' Finset.univ)
    have hne : ∀ j : Fin r, q' j ≠ qlast := by
      intro j hj
      exact hqlast (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩)
    have hsnoc : ∀ i : Fin (r + 1), (Fin.snoc q' qlast : Fin (r + 1) → ℚ) i = qlast →
        i = Fin.last r := by
      intro i hi
      by_cases hlast : i = Fin.last r
      · exact hlast
      · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hlast
        rw [Fin.snoc_castSucc] at hi
        exact absurd hi (hne j)
    refine ⟨Fin.snoc q' qlast, ?_, ?_⟩
    · intro a b hab
      by_cases ha : a = Fin.last r
      · subst ha
        rw [Fin.snoc_last] at hab
        exact (hsnoc b hab.symm).symm
      · by_cases hb : b = Fin.last r
        · subst hb
          rw [Fin.snoc_last] at hab
          exact hsnoc a hab
        · obtain ⟨ja, rfl⟩ := Fin.exists_castSucc_eq.mpr ha
          obtain ⟨jb, rfl⟩ := Fin.exists_castSucc_eq.mpr hb
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hab
          rw [hq'inj hab]
    · intro j
      by_cases hlast : j = Fin.last r
      · subst hlast
        rw [Fin.snoc_last]
        exact hPlast
      · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hlast
        rw [Fin.snoc_castSucc]
        exact hq' i

/-- **Prescribed rank with separated coordinates.**  Every finite real packet has arbitrarily close
packets of any prescribed positive rank, with all coordinates nonzero and pairwise distinct. -/
theorem exists_injective_exactRank_close {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (g : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g' : Fin n → ℝ, rationalCoordinateRank g' = k ∧ Function.Injective g' ∧
      (∀ j, g' j ≠ 0) ∧ (∀ j, dist (g' j) (g j) < ε) := by
  classical
  obtain ⟨r, rfl⟩ := exists_add_of_le hkn
  obtain ⟨b, hb, hbclose⟩ :=
    exists_linearIndependent_close k (fun i => g (Fin.castAdd r i)) ε hε
  have hb0 : b ⟨0, hk⟩ ≠ 0 := hb.ne_zero ⟨0, hk⟩
  obtain ⟨q, hqinj, hq⟩ := exists_injective_rat_choice
    (r := r) (fun j q => q ∉ ({0, 1} : Finset ℚ) ∧
      dist ((q : ℝ) * b ⟨0, hk⟩) (g (Fin.natAdd k j)) < ε)
    (by
      intro j s
      obtain ⟨q, hqs, hqclose⟩ := exists_rat_mul_close_notMem hb0 hε (g (Fin.natAdd k j))
        (s ∪ ({0, 1} : Finset ℚ))
      exact ⟨q, fun hmem => hqs (Finset.mem_union_left _ hmem),
        fun hmem => hqs (Finset.mem_union_right _ hmem), hqclose⟩)
  have hq0 : ∀ j, (q j : ℚ) ≠ 0 := fun j hj => (hq j).1 (by rw [hj]; simp)
  have hq1 : ∀ j, (q j : ℚ) ≠ 1 := fun j hj => (hq j).1 (by rw [hj]; simp)
  have hspan : Submodule.span ℚ (Set.range (Fin.append b fun j => (q j : ℝ) * b ⟨0, hk⟩))
      = Submodule.span ℚ (Set.range b) := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro z ⟨i, rfl⟩
      refine Fin.addCases (motive := fun i =>
        (Fin.append b fun j => (q j : ℝ) * b ⟨0, hk⟩) i ∈ Submodule.span ℚ (Set.range b))
        (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact Submodule.subset_span ⟨j, rfl⟩
      · rw [Fin.append_right]
        have hsmul : (q j : ℝ) * b ⟨0, hk⟩ = (q j : ℚ) • b ⟨0, hk⟩ := (Rat.smul_def _ _).symm
        rw [hsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨0, hk⟩, rfl⟩)
    · refine Submodule.span_le.2 ?_
      rintro z ⟨i, rfl⟩
      exact Submodule.subset_span ⟨Fin.castAdd r i, by rw [Fin.append_left]⟩
  have hheadtail : ∀ (i : Fin k) (j : Fin r), b i ≠ (q j : ℝ) * b ⟨0, hk⟩ := by
    intro i j hij
    by_cases hii0 : i = ⟨0, hk⟩
    · rw [hii0] at hij
      have hcontr : (1 - (q j : ℝ)) * b ⟨0, hk⟩ = 0 := by linear_combination hij
      rcases mul_eq_zero.mp hcontr with h | h
      · refine hq1 j ?_
        have hone : ((q j : ℚ) : ℝ) = 1 := by linarith
        exact_mod_cast hone
      · exact hb0 h
    · have hmem : b i ∈ Submodule.span ℚ (b '' {⟨0, hk⟩}) := by
        rw [hij]
        have hsmul : (q j : ℝ) * b ⟨0, hk⟩ = (q j : ℚ) • b ⟨0, hk⟩ := (Rat.smul_def _ _).symm
        rw [hsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨0, hk⟩, rfl, rfl⟩)
      exact hb.notMem_span_image (by simpa using hii0) hmem
  refine ⟨Fin.append b fun j => (q j : ℝ) * b ⟨0, hk⟩, ?_, ?_, ?_, ?_⟩
  · rw [rationalCoordinateRank, hspan, finrank_span_eq_card hb, Fintype.card_fin]
  · intro a c hac
    refine Fin.addCases (motive := fun a =>
      (Fin.append b fun j => (q j : ℝ) * b ⟨0, hk⟩) a
        = (Fin.append b fun j => (q j : ℝ) * b ⟨0, hk⟩) c → a = c) (fun i => ?_) (fun j => ?_) a hac
    · refine Fin.addCases (motive := fun c =>
        (Fin.append b fun j => (q j : ℝ) * b ⟨0, hk⟩) (Fin.castAdd r i)
          = (Fin.append b fun j => (q j : ℝ) * b ⟨0, hk⟩) c → Fin.castAdd r i = c)
        (fun i' => ?_) (fun j' => ?_) c
      · intro h
        rw [Fin.append_left, Fin.append_left] at h
        rw [hb.injective h]
      · intro h
        rw [Fin.append_left, Fin.append_right] at h
        exact absurd h (hheadtail i j')
    · refine Fin.addCases (motive := fun c =>
        (Fin.append b fun j' => (q j' : ℝ) * b ⟨0, hk⟩) (Fin.natAdd k j)
          = (Fin.append b fun j' => (q j' : ℝ) * b ⟨0, hk⟩) c → Fin.natAdd k j = c)
        (fun i' => ?_) (fun j' => ?_) c
      · intro h
        rw [Fin.append_right, Fin.append_left] at h
        exact absurd h.symm (hheadtail i' j)
      · intro h
        rw [Fin.append_right, Fin.append_right] at h
        have hqq : (q j : ℝ) = (q j' : ℝ) := mul_right_cancel₀ hb0 h
        have hqe : q j = q j' := by exact_mod_cast hqq
        rw [hqinj hqe]
  · intro j
    refine Fin.addCases (motive := fun j =>
      (Fin.append b fun j' => (q j' : ℝ) * b ⟨0, hk⟩) j ≠ 0) (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact hb.ne_zero i
    · rw [Fin.append_right]
      refine mul_ne_zero ?_ hb0
      exact_mod_cast hq0 i
  · intro i
    refine Fin.addCases (motive := fun i =>
      dist ((Fin.append b fun j' => (q j' : ℝ) * b ⟨0, hk⟩) i) (g i) < ε)
      (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact hbclose j
    · rw [Fin.append_right]
      exact (hq j).2

/-- **Simple spectra of prescribed temporal dimension.**  Every finite spectrum has arbitrarily
close simple spectra whose gap packet has any prescribed positive rank not exceeding the number of
gaps. -/
theorem exists_simpleSpectrum_close_gapRank {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (E : Fin (n + 1) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ E' : Fin (n + 1) → ℝ, Function.Injective E' ∧ (∀ i, dist (E' i) (E i) < ε) ∧
      rationalCoordinateRank (fun j : Fin n => E' j.succ - E' 0) = k := by
  obtain ⟨g', hrank, hginj, hgne, hgclose⟩ :=
    exists_injective_exactRank_close hk hkn (fun j : Fin n => E j.succ - E 0) hε
  refine ⟨Fin.cases (E 0) (fun j => E 0 + g' j), ?_, ?_, ?_⟩
  · intro a c hac
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨ja, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨jc, rfl⟩
    · rfl
    · exfalso
      simp only [Fin.cases_zero, Fin.cases_succ] at hac
      exact hgne jc (by linarith)
    · exfalso
      simp only [Fin.cases_zero, Fin.cases_succ] at hac
      exact hgne ja (by linarith)
    · simp only [Fin.cases_succ] at hac
      rw [hginj (by linarith : g' ja = g' jc)]
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simp only [Fin.cases_zero]
      simpa using hε
    · simp only [Fin.cases_succ]
      have hclose := hgclose j
      rw [Real.dist_eq] at hclose ⊢
      have hrewrite : E 0 + g' j - E j.succ = g' j - (E j.succ - E 0) := by ring
      rw [hrewrite]
      exact hclose
  · have hfun : (fun j : Fin n => (Fin.cases (E 0) (fun j => E 0 + g' j) : Fin (n + 1) → ℝ) j.succ
        - (Fin.cases (E 0) (fun j => E 0 + g' j) : Fin (n + 1) → ℝ) 0) = g' := by
      funext j
      simp only [Fin.cases_succ, Fin.cases_zero]
      ring
    rw [hfun]
    exact hrank

end

end GaloisForLFunctions.HTGeometry
