import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.AmpleChartRefinement

/-! Local ample families on a finite distinguished cover give a single ample family. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory.AmpleLocal

variable {Z : Scheme.{0}}

def Pack {ι : Type} (U : ι → Z.Opens) (G : ι → Fn Z) (W : Z.Opens) (S : Set (Fn Z)) : Prop :=
  ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ s : Fin (M + 1) → Fn Z, ∃ D : Fin (M + 1) → Z.Opens, (∀ j, Sc U G W N (s j)) ∧
    (∀ j, IsLoc (D j) W (s j)) ∧ (∀ z ∈ W, ∃ j, z ∈ D j) ∧ (∀ j, IsAffineOpen (D j)) ∧
    ∀ j, Gen (D j) (S ∪ Set.range fun m => s m * inv (s j))

/-- Equalize the powers of the bundle, extend the sections and compare their local ratios. -/
theorem glue_pack {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z} (hU : ∀ z, ∃ i, z ∈ U i) (hG : ∀ i z, IsUnit (G i z))
    [CompactSpace Z] [QuasiSeparatedSpace Z] (hT : ∀ i j, G i * inv (G j) ∈ Reg (U i ⊓ U j))
    {R : Type} [CommRing R] (φ : R →+* Fn Z) (hφ : ∀ r, φ r ∈ Reg ⊤) {Λ : Type} [Finite Λ] (a : Λ → R)
    (ha : Ideal.span (Set.range a) = ⊤) (W : Λ → Z.Opens) (hW : ∀ l, IsLoc (W l) ⊤ (φ (a l)))
    (H : ∀ l, Pack U G (W l) (insert (inv (φ (a l))) (Set.range φ))) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ σ : Fin (M + 1) → Fn Z, (∀ t, Sc U G ⊤ N (σ t)) ∧ (∀ z, ∃ t, IsUnit (σ t z)) ∧
      ∀ t D, IsLoc D ⊤ (σ t) → IsAffineOpen D ∧ Gen D (Set.range φ ∪ Set.range fun m => σ m * inv (σ t)) := by
  classical
  have := Fintype.ofFinite Λ
  choose N hN M s D hs hD cov aff gen using H
  have hd : ∀ l, ∃ d, ∏ l, N l = N l * (d + 1) := fun l => by
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ l)
    have : 0 < ∏ l, N l := Finset.prod_pos fun l _ => hN l
    cases e with
    | zero => omega
    | succ e => exact ⟨e, he⟩
  choose d hd using hd
  let T := Σ l, Fin (M l + 1) × Fin (M l + 1)
  have hsc : ∀ t : T, Sc U G (W t.1) (∏ l, N l) (s t.1 t.2.2 * s t.1 t.2.1 ^ d t.1) := fun t => by
    rw [hd t.1, mul_add, mul_one, add_comm]
    exact (hs _ _).mul ((hs _ _).pow _)
  choose k σ hσ eσ using fun t : T => (hsc t).extend hU hG hT (hφ _) (hW t.1)
  have covW : ∀ z, ∃ l, z ∈ W l := fun z => by
    by_contra hn
    have : Ideal.span (Set.range a) ≤ (IsLocalRing.maximalIdeal (Z.presheaf.stalk z)).comap
        ((Pi.evalRingHom _ z).comp φ) := Ideal.span_le.2 (by
      rintro _ ⟨l, rfl⟩ hu
      exact hn ⟨l, (hW l z).2 ⟨trivial, hu⟩⟩)
    rw [ha, top_le_iff, Ideal.comap_eq_top_iff] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top this
  have main : ∀ τ, Sc U G ⊤ (∏ l, N l) τ → ∀ E, IsLoc E ⊤ τ →
      IsAffineOpen E ∧ Gen E (Set.range φ ∪ Set.range fun m => σ m * inv τ) := by
    intro τ hτ E hE
    let B := Subring.closure (Set.range φ ∪ Set.range fun m => σ m * inv τ)
    have hB : B ≤ Reg E := Subring.closure_le.2 (by
      rintro x (⟨r, rfl⟩ | ⟨p, rfl⟩)
      · exact reg_mono le_top (hφ r)
      · exact Sc.ratio hU hG (hσ p) hτ hE)
    let ψ : R →+* B := φ.codRestrict B fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    have key : ∀ l, IsAffineOpen (W l ⊓ E) ∧ Gen (W l ⊓ E) _ := fun l =>
      extra_section hU hG (hs l) (hD l) (cov l) (aff l) (by
        rintro x (rfl | ⟨r, rfl⟩)
        · exact reg_inv (reg_mono le_top (hφ _)) fun z hz => (hW l).unit hz
        · exact reg_mono le_top (hφ r)) (gen l) (τ := τ) (d := d l) (by rw [← hd l]; exact hτ.mono le_top)
        (W := W l ⊓ E) fun z => ⟨fun hz => ⟨hz.1, hE.unit hz.2⟩, fun hz => ⟨hz.1, (hE z).2 ⟨trivial, hz.2⟩⟩⟩
    obtain ⟨h₁, h₂⟩ := local_global B hB (fun l => ψ (a l)) (by
        have := congrArg (Ideal.map ψ) ha
        rw [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at this
        exact top_le_iff.1 (this.ge.trans le_sup_right)) (fun l => W l ⊓ E)
      (fun l z => ⟨fun hz => ⟨hz.2, (hW l).unit hz.1⟩, fun hz => ⟨(hW l z).2 ⟨trivial, hz.2⟩, hz.1⟩⟩)
      (fun l => (key l).1) fun l => (key l).2.mono (by
        rintro x ((rfl | ⟨r, rfl⟩) | ⟨p, rfl⟩)
        · exact ⟨_, Subring.subset_closure (Or.inl rfl), fun _ _ => rfl⟩
        · exact ⟨_, Subring.subset_closure (Or.inr (ψ r).2), fun _ _ => rfl⟩
        · refine ⟨inv (φ (a l)) ^ k ⟨l, p⟩ * (σ ⟨l, p⟩ * inv τ),
            Subring.mul_mem _ (Subring.pow_mem _ (Subring.subset_closure (Set.mem_insert _ _)) _)
              (Subring.subset_closure (Or.inr (Subring.subset_closure (Or.inr ⟨⟨l, p⟩, rfl⟩)))), fun z hz => ?_⟩
          show s l p.2 z * s l p.1 z ^ d l * inv τ z =
            Ring.inverse (φ (a l) z) ^ k ⟨l, p⟩ * (σ ⟨l, p⟩ z * inv τ z)
          rw [eσ ⟨l, p⟩ z hz.1, mul_assoc (φ _ z ^ _), ← mul_assoc (Ring.inverse _ ^ _), ← mul_pow,
            Ring.inverse_mul_cancel _ ((hW l).unit hz.1), one_pow, one_mul]
          rfl)
    exact ⟨h₁, h₂.mono fun x hx => ⟨x, hx, fun _ _ => rfl⟩⟩
  let e : Fin (Fintype.card T + 1) ≃ Option T :=
    (finSuccEquiv _).trans (Fintype.equivFin T).symm.optionCongr
  let σ' : Option T → Fn Z := fun o => o.elim 0 σ
  have hσ' : ∀ o, Sc U G ⊤ (∏ l, N l) (σ' o) := fun o => by
    cases o with
    | none => exact Sc.zero _ _
    | some t => exact hσ t
  refine ⟨∏ l, N l, (Finset.prod_pos fun l _ => hN l : 0 < ∏ l, N l), Fintype.card T, fun t => σ' (e t), fun t => hσ' _,
    fun z => ?_, fun t E hE => ?_⟩
  · obtain ⟨l, hl⟩ := covW z
    obtain ⟨j, hj⟩ := cov l z hl
    refine ⟨e.symm (some ⟨l, j, j⟩), ?_⟩
    simp only [Equiv.apply_symm_apply]
    show IsUnit (σ ⟨l, j, j⟩ z)
    rw [eσ ⟨l, j, j⟩ z hl]
    exact (((hW l).unit hl).pow _).mul (((hD l j).unit hj).mul (((hD l j).unit hj).pow _))
  · obtain ⟨h₁, h₂⟩ := main _ (hσ' (e t)) E hE
    refine ⟨h₁, h₂.mono ?_⟩
    rintro x (hx | ⟨m, rfl⟩)
    · exact ⟨x, Subring.subset_closure (Or.inl hx), fun _ _ => rfl⟩
    · refine ⟨_, Subring.subset_closure (Or.inr ⟨e.symm (some m), ?_⟩), fun _ _ => rfl⟩
      simp only [Equiv.apply_symm_apply]
      rfl

end GlobalTheory.AmpleLocal
