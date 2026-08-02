import GaloisForLFunctions.HTGeometry.UniformJetPolyGroupFintype

/-!
# A jet polynomial with mixed `ψ`-degrees

Partitioning the monomials by their `ψ`-degree splits a jet polynomial into groups.  Each group is
handled by the non-flatness dichotomy as a whole — so cancellation inside it is harmless — and the
groups carry distinct `log`-degrees, so no cancellation is possible between them.

The residue of the whole polynomial is therefore the dominant group's residue, and it is nonzero.
This is eq. (19) in tube form with the nonvanishing intact.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The residue of a jet polynomial with mixed `ψ`-degrees, uniformly on a tube.** -/
theorem exists_tubeLimit_jetPoly_mixed_residue {M : ℝ} (hM : 0 < M) {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (K d : ℕ) (a : ι → Polynomial ℂ) (E : ι → Fin (K + 1) → ℕ)
    (hdeg : ∀ x, (a x).natDegree ≤ d) (hEinj : Function.Injective E) (ha : ∀ x, a x ≠ 0) :
    ∃ (p e : ℕ) (c : ℂ), c ≠ 0 ∧ TubeLimit M (fun σ t =>
      (∑ x : ι, ((a x).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E x i)
      / gammaShapeZ σ 0 (-(p : ℤ)) (e : ℤ) t) c := by
  classical
  -- the `ψ`-degree of each monomial, and the groups it cuts out
  set g : ι → ℕ := fun x => E x 0 with hg
  set S : Finset ℕ := Finset.univ.image g with hS
  haveI : Nonempty ↥S := by
    obtain ⟨x⟩ := ‹Nonempty ι›
    exact ⟨⟨g x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩⟩
  -- each group has a datum with nonzero residue
  have hgroup : ∀ γ : ↥S, ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ TubeLimit M (fun σ t =>
      (∑ x : {x : ι // g x = (γ : ℕ)},
          ((a (x : ι)).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E (x : ι) i)
        / gammaShapeZ σ 0 (-(p : ℤ)) ((γ : ℕ) : ℤ) t) c := by
    intro γ
    obtain ⟨x₀, hx₀mem, hx₀⟩ := Finset.mem_image.mp γ.2
    refine exists_tubeLimit_jetPolyGroup_datum_fintype hM K d (γ : ℕ)
      (fun x : {x : ι // g x = (γ : ℕ)} => a (x : ι))
      (fun x : {x : ι // g x = (γ : ℕ)} => E (x : ι))
      (fun x => hdeg _) ?_ (fun x => x.2) (x₀ := ⟨x₀, hx₀⟩) (ha _)
    intro x y hxy
    exact Subtype.ext (hEinj hxy)
  choose p c hc hlim using hgroup
  -- the groups are separated by their log degrees
  obtain ⟨β, hβ⟩ := exists_tubeLimit_logSeparated_residue hM
    (fun γ : ↥S => fun σ t => ∑ x : {x : ι // g x = (γ : ℕ)},
      ((a (x : ι)).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
      * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E (x : ι) i)
    p (fun γ : ↥S => (γ : ℕ)) c hc (fun x y hxy => Subtype.ext hxy) hlim
  refine ⟨p β, (β : ℕ), c β, hc β, ?_⟩
  refine hβ.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  refine congrArg (fun w => w / gammaShapeZ σ 0 (-(p β : ℤ)) (((β : ℕ)) : ℤ) t) ?_
  -- the group sums reassemble the whole sum
  set f : ι → ℂ := fun x => ((a x).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
    * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
        ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E x i with hf
  have hinner : ∀ γ : ↥S, ∑ x : {x : ι // g x = (γ : ℕ)}, f (x : ι)
      = ∑ x ∈ Finset.univ.filter (fun x : ι => g x = (γ : ℕ)), f x :=
    fun γ => (Finset.sum_subtype _ (fun x => by simp [Finset.mem_filter]) f).symm
  have houter : ∑ γ ∈ S, ∑ x ∈ Finset.univ.filter (fun x : ι => g x = γ), f x
      = ∑ x : ι, f x :=
    Finset.sum_fiberwise_of_maps_to (fun x _ => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) f
  calc ∑ γ : ↥S, ∑ x : {x : ι // g x = (γ : ℕ)}, f (x : ι)
      = ∑ γ : ↥S, ∑ x ∈ Finset.univ.filter (fun x : ι => g x = (γ : ℕ)), f x :=
        Finset.sum_congr rfl fun γ _ => hinner γ
    _ = ∑ γ ∈ S, ∑ x ∈ Finset.univ.filter (fun x : ι => g x = γ), f x :=
        Finset.sum_coe_sort S (fun γ : ℕ => ∑ x ∈ Finset.univ.filter (fun x : ι => g x = γ), f x)
    _ = ∑ x : ι, f x := houter

end

end GaloisForLFunctions.HTGeometry
