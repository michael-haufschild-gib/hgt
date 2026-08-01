import GaloisForLFunctions.HTGeometry.JetPolyLineDatum
import GaloisForLFunctions.HTGeometry.FullJetPolyDatum
import GaloisForLFunctions.HTGeometry.SupportReindex

/-!
# The datum of an arbitrary nonzero jet polynomial, logarithmic level included

Monomials in *all* digamma jets split into a power of `psi` — the logarithmic level — times a
monomial in the positive-order jets.  Grouping the monomials by their `psi`-degree gives finitely
many groups with pairwise distinct logarithmic degrees, each a nonzero polynomial in the positive
order jets, hence each with a datum.  Distinct logarithmic degrees cannot cancel, so the whole
polynomial has the residue of its dominant group.

This removes the last restriction from the coefficient hypothesis of the finite phase law: any
nonzero differential polynomial in the digamma jets, with complex constant coefficients, has a
residue against a `polyJetShape` with nonzero limit.
-/

open Filter Topology Complex Finset

namespace GaloisForLFunctions

/-- **The datum of a nonzero jet polynomial over all orders.** -/
theorem exists_full_jetPoly_datum {σ : ℝ} (hσ : 0 < σ) {M K : ℕ} (hM : 0 < M) (c : Fin M → ℂ)
    (E : Fin M → Fin (K + 1) → ℕ) (hc : ∀ α, c α ≠ 0) (hE : Function.Injective E) :
    ∃ (a b : ℕ) (r : ℂ), r ≠ 0 ∧ Tendsto (fun t : ℝ =>
      (∑ α : Fin M, c α * ∏ j : Fin (K + 1),
        iteratedDeriv (j : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α j)
        / polyJetShape σ a 0 b t) atTop (nhds r) := by
  classical
  -- the positive-order part of a monomial
  let g : Fin M → ℝ → ℂ := fun α t => c α * ∏ i : Fin K,
    iteratedDeriv ((i : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α i.succ
  let lg : Fin M → ℕ := fun α => E α 0
  let T : Finset ℕ := Finset.image lg Finset.univ
  have hTne : T.Nonempty := ⟨lg ⟨0, hM⟩, Finset.mem_image_of_mem lg (Finset.mem_univ _)⟩
  have hN : 0 < T.card := Finset.card_pos.mpr hTne
  let v : Fin T.card → ℕ := fun β => ((T.equivFin.symm β : {x // x ∈ T}) : ℕ)
  have hvinj : Function.Injective v := fun β γ hβγ =>
    T.equivFin.symm.injective (Subtype.ext hβγ)
  have hvmem : ∀ β, v β ∈ T := fun β => (T.equivFin.symm β).2
  -- each fibre of the logarithmic degree, reindexed by a `Fin`
  have hfib : ∀ β : Fin T.card, ∃ (M' : ℕ) (ι : Fin M' → Fin M), Function.Injective ι
      ∧ (∀ j, lg (ι j) = v β) ∧ (∀ α, lg α = v β → ∃ j, ι j = α)
      ∧ ∑ α ∈ Finset.univ.filter (fun α => lg α = v β), g α = ∑ j : Fin M', g (ι j) := by
    intro β
    obtain ⟨M', ι, hinj, hmem, hsurj, hsum⟩ :=
      exists_fin_reindex_of_finset (A := ℝ → ℂ) (Finset.univ.filter (fun α => lg α = v β)) g
    exact ⟨M', ι, hinj, fun j => (Finset.mem_filter.mp (hmem j)).2,
      fun α hα => hsurj α (Finset.mem_filter.mpr ⟨Finset.mem_univ α, hα⟩), hsum⟩
  choose M' ι hinj hfibmem hfibsurj hfibsum using hfib
  -- every fibre is nonempty, so its index type is
  have hM' : ∀ β, 0 < M' β := by
    intro β
    obtain ⟨α, -, hα⟩ := Finset.mem_image.mp (hvmem β)
    obtain ⟨j, -⟩ := hfibsurj β α hα
    exact Fin.pos j
  -- the exponents inside a fibre are distinct
  have hEfib : ∀ β, Function.Injective (fun j : Fin (M' β) => fun i : Fin K => E (ι β j) i.succ) := by
    intro β j k hjk
    refine hinj β ?_
    refine hE ?_
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [show E (ι β j) 0 = lg (ι β j) from rfl, show E (ι β k) 0 = lg (ι β k) from rfl,
        hfibmem β j, hfibmem β k]
    · exact congrFun hjk i
  -- each fibre sum is a nonzero jet polynomial, hence has a datum
  have hdat : ∀ β : Fin T.card, ∃ (p : ℕ) (r : ℂ), r ≠ 0 ∧
      Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * (∑ j : Fin (M' β), g (ι β j) t))
        atTop (nhds r) := by
    intro β
    have hne : jetPolyMv K (M' β) (fun j => c (ι β j))
        (fun j i => E (ι β j) i.succ) ≠ 0 :=
      jetPolyMv_ne_zero _ _ (hEfib β) (β := ⟨0, hM' β⟩) (hc _)
    obtain ⟨p, r, hr, hlim⟩ :=
      exists_jetPoly_datum_of_ne_zero hσ K (M' β) 0 (fun j => c (ι β j))
        (fun j i => E (ι β j) i.succ) (fun _ => Nat.zero_le _) hne
    exact ⟨p, r, hr, hlim⟩
  choose p r hr hdatlim using hdat
  -- the polynomial is the sum of its groups, weighted by powers of `psi`
  have hsplit : ∀ t : ℝ, (∑ α : Fin M, c α * ∏ j : Fin (K + 1),
      iteratedDeriv (j : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α j)
      = ∑ β : Fin T.card, Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ v β
          * (∑ j : Fin (M' β), g (ι β j) t) := by
    intro t
    have hmonomial : ∀ α : Fin M, c α * ∏ j : Fin (K + 1),
        iteratedDeriv (j : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E α j
        = Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ lg α * g α t := by
      intro α
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, iteratedDeriv_zero]
      ring
    rw [Finset.sum_congr rfl fun α _ => hmonomial α]
    have hmaps : ∀ α ∈ (Finset.univ : Finset (Fin M)),
        T.equivFin ⟨lg α, Finset.mem_image_of_mem lg (Finset.mem_univ α)⟩ ∈
          (Finset.univ : Finset (Fin T.card)) := fun α _ => Finset.mem_univ _
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun α => Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ lg α * g α t)]
    refine Finset.sum_congr rfl fun β _ => ?_
    have hfilter : (Finset.univ.filter fun α =>
          T.equivFin ⟨lg α, Finset.mem_image_of_mem lg (Finset.mem_univ α)⟩ = β)
        = Finset.univ.filter (fun α => lg α = v β) := by
      refine Finset.filter_congr fun α _ => ?_
      constructor
      · intro h
        have hsym : T.equivFin.symm β = ⟨lg α, Finset.mem_image_of_mem lg (Finset.mem_univ α)⟩ :=
          (Equiv.symm_apply_eq T.equivFin).mpr h.symm
        exact (congrArg (fun x : {x // x ∈ T} => (x : ℕ)) hsym).symm
      · intro h
        refine T.equivFin.symm.injective ?_
        rw [Equiv.symm_apply_apply]
        exact Subtype.ext (by simpa [v] using h)
    rw [hfilter]
    have hpull : ∑ α ∈ Finset.univ.filter (fun α => lg α = v β),
        Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ lg α * g α t
        = Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ v β
          * ∑ α ∈ Finset.univ.filter (fun α => lg α = v β), g α t := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [(Finset.mem_filter.mp hα).2]
    rw [hpull]
    congr 1
    have hev := congrFun (hfibsum β) t
    simpa [Finset.sum_apply] using hev
  obtain ⟨γ, hγ⟩ := exists_grouped_jetPoly_datum hσ hN
    (fun β t => ∑ j : Fin (M' β), g (ι β j) t) v hvinj p r hdatlim
  refine ⟨v γ, p γ, r γ, hr γ, ?_⟩
  refine hγ.congr fun t => ?_
  rw [hsplit t]

end GaloisForLFunctions
