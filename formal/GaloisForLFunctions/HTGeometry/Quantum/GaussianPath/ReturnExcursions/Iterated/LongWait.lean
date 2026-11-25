import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.PhysicalCharge

/-! # Deadline for the first genuinely long wait in chronological order -/

open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated
noncomputable section

/-- Until the first long wait begins, a bounded lookahead sees an
affordable date at every time. The occupation estimate thus pays for
the whole elapsed interval, including the last ascent. -/
theorem first_long (v σ : ℕ → ℝ) (A : Set ℝ) {W E G : ℝ}
    (hE : 1<E) (hr : ∀ i, v i≤σ i) (hg : ∀ i, v i+1≤v (i+1))
    (hpre : ∀ i, Icc (v i) (σ i) ⊆ A)
    (hpost : ∀ i, v (i+1)-σ i≤W → Icc (σ i) (v (i+1))⊆A)
    (hm : ∀ a T : ℝ, 0≤T → E*volume.real (A∩Icc a (a+T))≤T+G) (m : ℕ) :
    ∃ j : ℕ, W<v (m+j+1)-σ (m+j) ∧
      (∀ i<j, v (m+i+1)-σ (m+i)≤W) ∧ (E-1)*(σ (m+j)-v m)≤G := by
  have grows (j : ℕ) : v m+j≤v (m+j) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_succ,←add_assoc]
      exact (add_le_add_left ih 1).trans (hg _)
  have cover (j : ℕ) (hs : ∀ i<j, v (m+i+1)-σ (m+i)≤W) : Icc (v m) (σ (m+j))⊆A := by
    induction j with
    | zero => simpa only [Nat.add_zero] using hpre m
    | succ j ih =>
      intro t ht
      by_cases h : t≤σ (m+j)
      · exact ih (fun i hi => hs i (Nat.lt_succ_of_lt hi)) ⟨ht.1,h⟩
      by_cases h' : t≤v (m+j+1)
      · exact hpost _ (hs j (Nat.lt_succ_self _)) ⟨le_of_not_ge h,h'⟩
      · exact hpre _ ⟨le_of_not_ge h',ht.2⟩
  have pay (j : ℕ) (hs : ∀ i<j, v (m+i+1)-σ (m+i)≤W) : (E-1)*(σ (m+j)-v m)≤G := by
    let T := σ (m+j)-v m
    have hT : 0≤T := by linarith only [grows j, hr (m+j), Nat.cast_nonneg (α:=ℝ) j]
    have h := hm (v m) T hT
    have he : v m+T=σ (m+j) := by dsimp only [T]; ring
    rw [he,inter_eq_right.mpr (cover j hs),Real.volume_real_Icc_of_le (sub_nonneg.mp hT)] at h
    change E*T≤T+G at h
    change (E-1)*T≤G
    linarith only [h]
  have ex : ∃ j : ℕ, W<v (m+j+1)-σ (m+j) := by
    by_contra! hall
    obtain ⟨n,hn⟩ := exists_nat_gt (G/(E-1))
    have h := pay n (fun i _ => hall i)
    have hl : (n:ℝ)≤σ (m+n)-v m := by linarith only [grows n,hr (m+n)]
    exact ((div_lt_iff₀ (sub_pos.mpr hE)).mp hn).not_ge
      ((mul_le_mul_of_nonneg_right hl (sub_nonneg.mpr hE.le)).trans (by rwa [mul_comm] at h))
  classical
  have before (i : ℕ) (hi : i<Nat.find ex) : v (m+i+1)-σ (m+i)≤W :=
    le_of_not_gt (Nat.find_min ex hi)
  exact ⟨Nat.find ex,Nat.find_spec ex,before,pay _ before⟩

/-- From any recorded low visit, the first excursion whose actual
post-crossing wait exceeds 2^b starts its wait by G/(2^e-1).
All intervening waits are explicitly shorter or equal. -/
theorem gaussian_first_long_wait :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let D := 2^N
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let G := (2:ℝ)^(D^c)
      ∀ s≤P/2, let v := lowDate H P s
        let σ := highDate H P s
        ∀ b e m : ℕ, 0<e → 16*(b+e)≤7*D →
          ∃ j : ℕ, (2:ℝ)^b<v (m+j+1)-σ (m+j) ∧
            (∀ i<j, v (m+i+1)-σ (m+i)≤(2:ℝ)^b) ∧
            ((2:ℝ)^e-1)*(σ (m+j)-v m)≤G := by
  obtain ⟨c,hwin⟩ := gaussian_full_budget_robust_windows
  obtain ⟨_,hcycle⟩ := gaussian_cycle_windows
  refine ⟨c,?_⟩
  filter_upwards [hwin,hcycle] with ω h hc
  filter_upwards [h,hc] with k hk hck
  intro N D H P G s hs v σ b e m he hbe
  obtain ⟨hd,_⟩ := hck s hs
  let W := (2:ℝ)^b
  have hsP := hs.trans (Nat.div_le_self P 2)
  apply first_long v σ (robustWindowHits H P W) (one_lt_pow₀ (by norm_num) he.ne')
    (fun i => (hd i).1.le) (fun i => by have h := hd i; linarith only [h.1,h.2.2.2.2.1]) _ _
    (hk.2 b e hbe) m
  · intro i t ht
    have ht' : orbitCircuitDistance H P t≤9/80 := by
      rcases ht.2.lt_or_eq with hlt|rfl
      · exact le_of_not_ge (fun hh => hlt.not_ge ((hd i).2.2.1.2 ⟨ht.1,hh⟩))
      · exact (hd i).2.1.le
    exact ⟨t,⟨le_rfl,le_add_of_nonneg_right (by dsimp only [W]; positivity)⟩,ht'.trans (by norm_num)⟩
  · intro i hshort t ht
    exact ⟨v (i+1),⟨ht.2,by linarith only [ht.1,hshort]⟩,
      (low_at_larger_budget H P s (i+1) hsP).trans (by norm_num)⟩

#print axioms gaussian_first_long_wait
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated
