import GaloisForLFunctions.HTGeometry.TripticSeparatedPrincipalPart

/-!
# A base-point-free formula for the principal part

The finitely supported separation of the coefficient array can be evaluated at the base point
itself, and both separated values are then transverse sums of the two boundary functions:

`c_ℓ(F, w) = − Σ_{k ≥ 0} c_ℓ(Δ_τ F, w + kτ) + Σ_{j ≥ 1} c_ℓ(Δ_σ F, w − jσ)`.

Both sums are finite — the boundary coefficient families along an orbit are finitely supported — and
neither depends on a choice of orbit representative: every Laurent coefficient of a source of
vanishing orbital divisor is read off from its two boundary functions alone.

This is the formula the atom coefficients are defined by.

* `laurentCoeff_eq_transverse_sums`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

variable {F : ℂ → ℂ} {τ σ : ℂ}

/-- **The base-point-free principal-part formula.** -/
theorem laurentCoeff_eq_transverse_sums
    (hF : MeromorphicOn F Set.univ)
    (hper : ∀ z : ℂ, F (z + 1) = F z)
    {Cst : ℂ} (hmixed : ∀ z : ℂ, F (z + τ + σ) - F (z + τ) - F (z + σ) + F z = Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    {ℓ : ℤ} (hℓ : ℓ < 0) (w : ℂ)
    (hvanish : ∑ᶠ m : ℤ, laurentCoeff (fun z => F (z + σ) - F z) (w + (m : ℂ) * σ) ℓ = 0) :
    laurentCoeff F w ℓ
      = -(∑ᶠ k : ℕ, laurentCoeff (fun z => F (z + τ) - F z) (w + ((k : ℤ) : ℂ) * τ) ℓ)
        + ∑ᶠ j : ℕ, laurentCoeff (fun z => F (z + σ) - F z)
            (w + ((-((j : ℤ) + 1) : ℤ) : ℂ) * σ) ℓ := by
  classical
  set Uτ : ℂ → ℂ := fun z => F (z + σ) - F z with hUτdef
  set Uσ : ℂ → ℂ := fun z => F (z + τ) - F z with hUσdef
  have hUτmero : MeromorphicOn Uτ Set.univ := fun z _ =>
    (meromorphicAt_comp_add.mpr (hF (z + σ) (Set.mem_univ _))).sub (hF z (Set.mem_univ z))
  have hUσmero : MeromorphicOn Uσ Set.univ := fun z _ =>
    (meromorphicAt_comp_add.mpr (hF (z + τ) (Set.mem_univ _))).sub (hF z (Set.mem_univ z))
  have hUper1 : ∀ h : ℂ, ∀ a : ℂ,
      laurentCoeff (fun z => F (z + h) - F z) (a + 1) ℓ
        = laurentCoeff (fun z => F (z + h) - F z) a ℓ := by
    intro h a
    have hfun : (fun z => F (z + 1 + h) - F (z + 1)) = fun z => F (z + h) - F z := by
      funext z
      rw [show z + 1 + h = z + h + 1 from by ring, hper (z + h), hper z]
    calc laurentCoeff (fun z => F (z + h) - F z) (a + 1) ℓ
        = laurentCoeff (fun z => F (z + 1 + h) - F (z + 1)) a ℓ :=
          (laurentCoeff_comp_add (fun z => F (z + h) - F z) a 1 ℓ).symm
      _ = laurentCoeff (fun z => F (z + h) - F z) a ℓ := by rw [hfun]
  have hUτper1 : ∀ a : ℂ, laurentCoeff Uτ (a + 1) ℓ = laurentCoeff Uτ a ℓ := hUper1 σ
  have hUσper1 : ∀ a : ℂ, laurentCoeff Uσ (a + 1) ℓ = laurentCoeff Uσ a ℓ := hUper1 τ
  have hUτperτ : ∀ a : ℂ, laurentCoeff Uτ (a + τ) ℓ = laurentCoeff Uτ a ℓ := by
    intro a
    have hfun : (fun z => Uτ (z + τ)) = fun z => Uτ z + Cst := by
      funext z
      simp only [hUτdef]
      have h := hmixed z
      linear_combination h
    calc laurentCoeff Uτ (a + τ) ℓ
        = laurentCoeff (fun z => Uτ (z + τ)) a ℓ := (laurentCoeff_comp_add Uτ a τ ℓ).symm
      _ = laurentCoeff (fun z => Uτ z + Cst) a ℓ := by rw [hfun]
      _ = laurentCoeff Uτ a ℓ := laurentCoeff_add_const (hUτmero a (Set.mem_univ a)) Cst hℓ
  have hUσperσ : ∀ a : ℂ, laurentCoeff Uσ (a + σ) ℓ = laurentCoeff Uσ a ℓ := by
    intro a
    have hfun : (fun z => Uσ (z + σ)) = fun z => Uσ z + Cst := by
      funext z
      simp only [hUσdef]
      have h := hmixed z
      rw [show z + τ + σ = z + σ + τ from by ring] at h
      linear_combination h
    calc laurentCoeff Uσ (a + σ) ℓ
        = laurentCoeff (fun z => Uσ (z + σ)) a ℓ := (laurentCoeff_comp_add Uσ a σ ℓ).symm
      _ = laurentCoeff (fun z => Uσ z + Cst) a ℓ := by rw [hfun]
      _ = laurentCoeff Uσ a ℓ := laurentCoeff_add_const (hUσmero a (Set.mem_univ a)) Cst hℓ
  set cc : ℤ → ℤ → ℂ := fun n m => laurentCoeff F (w + (n : ℂ) * τ + (m : ℂ) * σ) ℓ with hccdef
  set B : ℤ → ℂ := fun m => laurentCoeff Uτ (w + (m : ℂ) * σ) ℓ with hBdef
  set A : ℤ → ℂ := fun n => laurentCoeff Uσ (w + (n : ℂ) * τ) ℓ with hAdef
  have hBcol : ∀ n m : ℤ, cc n (m + 1) - cc n m = B m := by
    intro n m
    have hstep : laurentCoeff Uτ (w + (n : ℂ) * τ + (m : ℂ) * σ) ℓ = cc n (m + 1) - cc n m := by
      rw [hUτdef, laurentCoeff_shiftDiff hF σ _ ℓ, hccdef]
      congr 2
      push_cast
      ring
    rw [← hstep, hBdef]
    have hmove : w + (n : ℂ) * τ + (m : ℂ) * σ = (w + (m : ℂ) * σ) + (n : ℂ) * τ := by ring
    rw [hmove, laurentCoeff_add_zsmul_of_period hUτperτ]
  have hArow : ∀ n m : ℤ, cc (n + 1) m - cc n m = A n := by
    intro n m
    have hstep : laurentCoeff Uσ (w + (n : ℂ) * τ + (m : ℂ) * σ) ℓ = cc (n + 1) m - cc n m := by
      rw [hUσdef, laurentCoeff_shiftDiff hF τ _ ℓ, hccdef]
      congr 2
      push_cast
      ring
    rw [← hstep, hAdef]
    have hmove : w + (n : ℂ) * τ + (m : ℂ) * σ = (w + (n : ℂ) * τ) + (m : ℂ) * σ := by ring
    rw [hmove, laurentCoeff_add_zsmul_of_period hUσperσ]
  have hindepBA : ∀ m n j : ℤ, (m : ℂ) * σ + (n : ℂ) * τ + (j : ℂ) = 0 →
      m = 0 ∧ n = 0 ∧ j = 0 := by
    intro m n j h
    obtain ⟨h1, h2, h3⟩ := hindep n m j (by linear_combination h)
    exact ⟨h2, h1, h3⟩
  have hBfin : {m : ℤ | B m ≠ 0}.Finite :=
    finite_setOf_laurentCoeff_ne_zero_orbit hUτmero hℓ hτ hUτper1 hUτperτ hindepBA w
  have hAfin : {n : ℤ | A n ≠ 0}.Finite :=
    finite_setOf_laurentCoeff_ne_zero_orbit hUσmero hℓ hσ hUσper1 hUσperσ hindep w
  obtain ⟨N₁, hN₁⟩ := exists_symmetric_bound_of_finite_support hAfin
  obtain ⟨N₂, hN₂⟩ := exists_symmetric_bound_of_finite_support hBfin
  set N : ℕ := max N₁ N₂ with hNdef
  have hAvanish : ∀ n : ℤ, ((N : ℤ) ≤ n ∨ n < -(N : ℤ)) → A n = 0 := by
    intro n hn
    refine hN₁ n ?_
    have h1 : (N₁ : ℤ) ≤ (N : ℤ) := by exact_mod_cast le_max_left N₁ N₂
    omega
  have hBvanish : ∀ m : ℤ, ((N : ℤ) ≤ m ∨ m < -(N : ℤ)) → B m = 0 := by
    intro m hm
    refine hN₂ m ?_
    have h1 : (N₂ : ℤ) ≤ (N : ℤ) := by exact_mod_cast le_max_right N₁ N₂
    omega
  have hsuppA : Function.support A ⊆ (Finset.Ico (-(N : ℤ)) (N : ℤ) : Finset ℤ) := by
    intro n hn
    simp only [Finset.coe_Ico, Set.mem_Ico]
    by_contra hcon
    exact hn (hAvanish n (by omega))
  have hsuppB : Function.support B ⊆ (Finset.Ico (-(N : ℤ)) (N : ℤ) : Finset ℤ) := by
    intro m hm
    simp only [Finset.coe_Ico, Set.mem_Ico]
    by_contra hcon
    exact hm (hBvanish m (by omega))
  have hsumA : ∑ᶠ n : ℤ, A n = cc (N : ℤ) 0 - cc (-(N : ℤ)) 0 := by
    rw [finsum_eq_sum_of_support_subset A hsuppA]
    rw [Finset.sum_congr rfl (fun n _ => (hArow n 0).symm)]
    exact sum_Ico_increment_telescope (fun n => cc n 0) N
  have hsumB : ∑ᶠ m : ℤ, B m = cc 0 (N : ℤ) - cc 0 (-(N : ℤ)) := by
    rw [finsum_eq_sum_of_support_subset B hsuppB]
    rw [Finset.sum_congr rfl (fun m _ => (hBcol 0 m).symm)]
    exact sum_Ico_increment_telescope (fun m => cc 0 m) N
  have hcorner : cc (N : ℤ) 0 + cc 0 (-(N : ℤ)) - cc 0 0 = 0 := by
    have hsep : ∀ n m : ℤ, cc n m = cc n 0 + (cc 0 m - cc 0 0) :=
      GaloisForLFunctions.additively_separable_of_indep_increments cc B hBcol
    have haUp : ∀ n : ℤ, (N : ℤ) ≤ n → cc n 0 = cc (N : ℤ) 0 :=
      eq_of_forall_ge_increment_zero (d := fun n => cc n 0) (N := (N : ℤ))
        (fun n hn => by
          have := hArow n 0
          rw [hAvanish n (Or.inl hn)] at this
          linear_combination this)
    have hbDown : ∀ m : ℤ, m ≤ -(N : ℤ) → cc 0 m = cc 0 (-(N : ℤ)) :=
      eq_of_forall_le_increment_zero (d := fun m => cc 0 m) (N := -(N : ℤ))
        (fun m hm => by
          have := hBcol 0 m
          rw [hBvanish m (Or.inr hm)] at this
          linear_combination this)
    have hFper : ∀ a : ℂ, laurentCoeff F (a + 1) ℓ = laurentCoeff F a ℓ := by
      intro a
      have hfun : (fun z => F (z + 1)) = F := funext hper
      calc laurentCoeff F (a + 1) ℓ
          = laurentCoeff (fun z => F (z + 1)) a ℓ := (laurentCoeff_comp_add F a 1 ℓ).symm
        _ = laurentCoeff F a ℓ := by rw [hfun]
    refine laurentCoeff_const_eq_zero_of_mixedQuadrant hF hℓ hFper hτ hσ hindep w
      (ε := 1) (Or.inl rfl) _ N ?_
    intro n m hn hm
    have hval : laurentCoeff F (w + ((1 * n : ℤ) : ℂ) * τ + ((1 * m : ℤ) : ℂ) * σ) ℓ = cc n m := by
      rw [hccdef]
      congr 2 <;> push_cast <;> ring
    rw [hval, hsep n m, haUp n hn, hbDown m hm]
    ring
  -- the two total masses vanish
  have hBzero : ∑ᶠ m : ℤ, B m = 0 := hvanish
  have hAzero : ∑ᶠ n : ℤ, A n = 0 := by
    have hrecip := triptic_orbit_residue_reciprocity hF hper hmixed hτ hσ hindep w hℓ
    rw [← hrecip]
    exact hBzero
  have hAends : cc (N : ℤ) 0 = cc (-(N : ℤ)) 0 := by
    rw [hsumA] at hAzero
    linear_combination hAzero
  have hBends : cc 0 (N : ℤ) = cc 0 (-(N : ℤ)) := by
    rw [hsumB] at hBzero
    linear_combination hBzero
  -- the two transverse sums
  have hrowsum : (∑ᶠ k : ℕ, A (k : ℤ)) = cc (N : ℤ) 0 - cc 0 0 := by
    have hsupp : Function.support (fun k : ℕ => A (k : ℤ)) ⊆ (Finset.range N : Finset ℕ) := by
      intro k hk
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hcon
      exact hk (hAvanish (k : ℤ) (Or.inl (by omega)))
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    have hterm : ∀ k ∈ Finset.range N,
        A (k : ℤ) = (fun i : ℕ => cc (i : ℤ) 0) (k + 1) - (fun i : ℕ => cc (i : ℤ) 0) k := by
      intro k _
      have := hArow (k : ℤ) 0
      simp only
      rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring]
      linear_combination -this
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun i : ℕ => cc (i : ℤ) 0) N]
    simp
  have hcolsum : (∑ᶠ j : ℕ, B (-((j : ℤ) + 1))) = cc 0 0 - cc 0 (-(N : ℤ)) := by
    have hsupp : Function.support (fun j : ℕ => B (-((j : ℤ) + 1)))
        ⊆ (Finset.range N : Finset ℕ) := by
      intro j hj
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hcon
      exact hj (hBvanish (-((j : ℤ) + 1)) (Or.inr (by omega)))
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    have hterm : ∀ j ∈ Finset.range N, B (-((j : ℤ) + 1))
        = (fun i : ℕ => cc 0 (-(i : ℤ))) j - (fun i : ℕ => cc 0 (-(i : ℤ))) (j + 1) := by
      intro j _
      have := hBcol 0 (-((j : ℤ) + 1))
      simp only
      rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 from by push_cast; ring]
      rw [show -((j : ℤ) + 1) + 1 = -(j : ℤ) from by ring] at this
      linear_combination -this
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' (fun i : ℕ => cc 0 (-(i : ℤ))) N]
    simp
  -- assemble
  have hAcast : ∀ k : ℕ, laurentCoeff Uσ (w + ((k : ℤ) : ℂ) * τ) ℓ = A (k : ℤ) := fun k => rfl
  have hBcast : ∀ j : ℕ, laurentCoeff Uτ (w + ((-((j : ℤ) + 1) : ℤ) : ℂ) * σ) ℓ
      = B (-((j : ℤ) + 1)) := fun j => rfl
  have hc00 : laurentCoeff F w ℓ = cc 0 0 := by
    rw [hccdef]
    norm_num
  rw [hc00]
  simp only [hUσdef, hUτdef] at *
  rw [show (∑ᶠ k : ℕ, laurentCoeff Uσ (w + ((k : ℤ) : ℂ) * τ) ℓ) = ∑ᶠ k : ℕ, A (k : ℤ) from by
    exact finsum_congr hAcast]
  rw [show (∑ᶠ j : ℕ, laurentCoeff Uτ (w + ((-((j : ℤ) + 1) : ℤ) : ℂ) * σ) ℓ)
      = ∑ᶠ j : ℕ, B (-((j : ℤ) + 1)) from by exact finsum_congr hBcast]
  rw [hrowsum, hcolsum]
  linear_combination hcorner

end

end GaloisForLFunctions.HTGeometry
