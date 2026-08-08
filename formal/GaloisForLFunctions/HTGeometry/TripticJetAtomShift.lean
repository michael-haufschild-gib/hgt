import GaloisForLFunctions.HTGeometry.TripticJetAtom

/-!
# The shift law of the higher atoms

The zero set of theta is closed, so the line-atom shift `A(z+σ) = A(z) − 2πi` holds on an open set.
Two functions agreeing on an open set have the same jets there, so every derivative of the atom
satisfies the same law with the constant differentiated away:

`A⁽ʲ⁾(z+σ) = A⁽ʲ⁾(z)` for `j ≥ 1`, and the original law for `j = 0`.

Consequently the mixed second difference of every jet atom vanishes off the countable set of its own
poles and their `τ`-translates: the atoms are members of the mixed-constraint class wherever they are
finite.

* `iteratedDeriv_succ_sub_const` — jets of positive order ignore an additive constant;
* `atomPoleSet`, `countable_atomPoleSet`, `isOpen_compl_atomPoleSet`;
* `jetAtom_shift_succ`, `jetAtom_mixed_eq_zero`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

variable {σ : ℂ}

/-- Jets of positive order do not see an additive constant. -/
theorem iteratedDeriv_succ_sub_const (f : ℂ → ℂ) (c : ℂ) (j : ℕ) :
    iteratedDeriv (j + 1) (fun w => f w - c) = iteratedDeriv (j + 1) f := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  congr 1
  funext u
  exact deriv_sub_const c

/-- The pole set of the line atom through `q`. -/
def atomPoleSet (σ q : ℂ) : Set ℂ :=
  {z : ℂ | ∃ m n : ℤ, z = q + thetaHalfPeriod σ + (m : ℂ) + (n : ℂ) * σ}

theorem countable_atomPoleSet (σ q : ℂ) : (atomPoleSet σ q).Countable := by
  have hsub : atomPoleSet σ q ⊆
      Set.range fun t : ℤ × ℤ => q + thetaHalfPeriod σ + (t.1 : ℂ) + (t.2 : ℂ) * σ := by
    rintro z ⟨m, n, hmn⟩
    exact ⟨(m, n), hmn.symm⟩
  exact Set.Countable.mono hsub (Set.countable_range _)

theorem mem_atomPoleSet_iff (hσ : 0 < σ.im) (q z : ℂ) :
    z ∈ atomPoleSet σ q ↔ jacobiTheta₂ (z - q) σ = 0 := by
  rw [atomPoleSet, Set.mem_setOf_eq, jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice hσ]
  constructor
  · rintro ⟨m, n, hmn⟩
    exact ⟨m, n, by linear_combination hmn⟩
  · rintro ⟨m, n, hmn⟩
    exact ⟨m, n, by linear_combination hmn⟩

theorem isOpen_compl_atomPoleSet (hσ : 0 < σ.im) (q : ℂ) : IsOpen (atomPoleSet σ q)ᶜ := by
  have hset : (atomPoleSet σ q)ᶜ = (fun z : ℂ => jacobiTheta₂ (z - q) σ) ⁻¹' {0}ᶜ := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
    rw [mem_atomPoleSet_iff hσ q z]
  rw [hset]
  refine IsOpen.preimage ?_ isOpen_compl_singleton
  have hdiff : Differentiable ℂ fun z : ℂ => jacobiTheta₂ (z - q) σ := fun z =>
    ((hasDerivAt_jacobiTheta₂_fst (z - q) hσ).differentiableAt).comp z
      (differentiableAt_id.sub_const q)
  exact hdiff.continuous

/-- **Every jet of positive order is `σ`-periodic off the poles.** -/
theorem jetAtom_shift_succ (hσ : 0 < σ.im) (q : ℂ) (j : ℕ) {z : ℂ} (hz : z ∉ atomPoleSet σ q) :
    jetAtom σ q (j + 1) (z + σ) = jetAtom σ q (j + 1) z := by
  have hopen := isOpen_compl_atomPoleSet hσ q
  have hev : (fun w => lineAtom σ q (w + σ)) =ᶠ[nhds z] fun w => lineAtom σ q w
      - 2 * (Real.pi : ℂ) * Complex.I := by
    filter_upwards [hopen.mem_nhds hz] with u hu
    refine lineAtom_shift hσ q ?_
    intro hcon
    exact hu ((mem_atomPoleSet_iff hσ q u).mpr hcon)
  have hjet : iteratedDeriv (j + 1) (fun w => lineAtom σ q (w + σ)) z
      = iteratedDeriv (j + 1) (fun w => lineAtom σ q w - 2 * (Real.pi : ℂ) * Complex.I) z :=
    Filter.EventuallyEq.iteratedDeriv_eq (j + 1) hev
  have hcomp : iteratedDeriv (j + 1) (fun w => lineAtom σ q (w + σ)) z
      = iteratedDeriv (j + 1) (lineAtom σ q) (z + σ) := by
    rw [iteratedDeriv_comp_add_const (j + 1) (lineAtom σ q) σ]
  show iteratedDeriv (j + 1) (lineAtom σ q) (z + σ) = iteratedDeriv (j + 1) (lineAtom σ q) z
  rw [← hcomp, hjet, iteratedDeriv_succ_sub_const (lineAtom σ q) (2 * (Real.pi : ℂ) * Complex.I) j]

/-- **Every jet atom has vanishing mixed second difference off its poles.** -/
theorem jetAtom_mixed_eq_zero (hσ : 0 < σ.im) (q τ : ℂ) (j : ℕ) {z : ℂ}
    (hz : z ∉ atomPoleSet σ q) (hzτ : z + τ ∉ atomPoleSet σ q) :
    jetAtom σ q j (z + τ + σ) - jetAtom σ q j (z + τ)
      - (jetAtom σ q j (z + σ) - jetAtom σ q j z) = 0 := by
  cases j with
  | zero =>
      have h1 : jetAtom σ q 0 (z + τ + σ) = jetAtom σ q 0 (z + τ)
          - 2 * (Real.pi : ℂ) * Complex.I := by
        simp only [jetAtom, iteratedDeriv_zero]
        refine lineAtom_shift hσ q ?_
        intro hcon
        exact hzτ ((mem_atomPoleSet_iff hσ q (z + τ)).mpr hcon)
      have h2 : jetAtom σ q 0 (z + σ) = jetAtom σ q 0 z - 2 * (Real.pi : ℂ) * Complex.I := by
        simp only [jetAtom, iteratedDeriv_zero]
        refine lineAtom_shift hσ q ?_
        intro hcon
        exact hz ((mem_atomPoleSet_iff hσ q z).mpr hcon)
      rw [h1, h2]
      ring
  | succ k =>
      rw [jetAtom_shift_succ hσ q k hzτ, jetAtom_shift_succ hσ q k hz]
      ring

/-- **Every jet atom is `1`-periodic.** -/
theorem jetAtom_periodic_one (σ q : ℂ) (j : ℕ) (z : ℂ) :
    jetAtom σ q j (z + 1) = jetAtom σ q j z :=
  jetAtom_periodic σ q j z

end

end GaloisForLFunctions.HTGeometry
