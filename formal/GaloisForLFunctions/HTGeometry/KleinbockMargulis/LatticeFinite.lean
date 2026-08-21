import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LatticeNorm

/-!
# Only finitely many lattices are short

For an invertible `A` and a threshold `ρ`, only finitely many rational subspaces `W ⊆ ℚ^k` satisfy
`‖A(W ∩ ℤ^k)‖ < ρ`.  This is condition (A3) of Kleinbock–Margulis §4 for the poset of §5.

The proof encodes `W` by its rank together with its integral Plücker vector, padded to the
rank-independent index type `Fin k → Fin k`.  The encoding is injective because the Plücker
coordinates determine the span, and its image is bounded because a minor of `V` is a combination
of the minors of `AV` with coefficients products of entries of `A⁻¹`.

## Main results

* `latticeCode_injective` — the encoding determines the subspace.
* `finite_latticeWedgeNorm_lt` — condition (A3).
-/

open Matrix Finset Module Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {k : ℕ}

/-! ### Plücker coordinates commute with ring maps -/

theorem plucker_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {j : ℕ}
    (V : Fin j → (Fin k → R)) (σ : Fin j → Fin k) :
    plucker (fun a i => φ (V a i)) σ = φ (plucker V σ) := by
  rw [plucker, plucker]
  rw [show (Matrix.of fun a b => φ (V a (σ b)))
      = φ.mapMatrix (Matrix.of fun a b => V a (σ b)) from by ext a b; simp]
  exact (RingHom.map_det φ (Matrix.of fun a b => V a (σ b))).symm

theorem plucker_intToRat {j : ℕ} (V : Fin j → (Fin k → ℤ)) (σ : Fin j → Fin k) :
    plucker (fun a => intToRat (V a)) σ = ((plucker V σ : ℤ) : ℚ) :=
  plucker_map (Int.castRingHom ℚ) V σ

theorem plucker_intToReal {j : ℕ} (V : Fin j → (Fin k → ℤ)) (σ : Fin j → Fin k) :
    plucker (fun a => intToReal (V a)) σ = ((plucker V σ : ℤ) : ℝ) :=
  plucker_map (Int.castRingHom ℝ) V σ

/-! ### The rank-independent Plücker encoding -/

theorem latticeRank_le (W : Submodule ℚ (Fin k → ℚ)) : latticeRank W ≤ k := by
  rw [latticeRank_eq_finrank]
  have h1 : Module.finrank ℚ W ≤ Module.finrank ℚ (Fin k → ℚ) := Submodule.finrank_le W
  simpa [Module.finrank_fin_fun] using h1

/-- The Plücker vector of the chosen basis, reindexed by maps `Fin k → Fin k` so as to live in a
type independent of the rank. -/
noncomputable def padPlucker (W : Submodule ℚ (Fin k → ℚ)) : (Fin k → Fin k) → ℤ :=
  fun σ => plucker (latticeBasis W) fun b => σ (Fin.castLE (latticeRank_le W) b)

/-- The complete combinatorial encoding of a rational subspace. -/
noncomputable def latticeCode (W : Submodule ℚ (Fin k → ℚ)) : ℕ × ((Fin k → Fin k) → ℤ) :=
  (latticeRank W, padPlucker W)

theorem exists_extend_castLE {j : ℕ} (hj : j ≤ k) (hk : 0 < k) (σ' : Fin j → Fin k) :
    ∃ σ : Fin k → Fin k, ∀ b : Fin j, σ (Fin.castLE hj b) = σ' b := by
  classical
  refine ⟨fun b => if h : (b : ℕ) < j then σ' ⟨b, h⟩ else ⟨0, hk⟩, fun b => ?_⟩
  have hlt : ((Fin.castLE hj b : Fin k) : ℕ) < j := b.isLt
  simp only [dif_pos hlt]
  congr 1

/-- The encoding determines the subspace. -/
theorem latticeCode_injective (hk : 0 < k) {W W' : Submodule ℚ (Fin k → ℚ)}
    (h : latticeCode W = latticeCode W') : W = W' := by
  have hr : latticeRank W = latticeRank W' := congrArg Prod.fst h
  have hp : padPlucker W = padPlucker W' := congrArg Prod.snd h
  have hZ : ∀ σ : Fin (latticeRank W) → Fin k,
      plucker (latticeBasis W) σ
        = plucker (latticeBasis W') fun b => σ (Fin.cast hr.symm b) := by
    intro σ
    obtain ⟨s, hs⟩ := exists_extend_castLE (latticeRank_le W) hk σ
    have h1 : plucker (latticeBasis W) σ = padPlucker W s := by
      rw [padPlucker]
      congr 1
      funext b
      rw [hs]
    have h2 : padPlucker W' s
        = plucker (latticeBasis W') fun b => σ (Fin.cast hr.symm b) := by
      rw [padPlucker]
      congr 1
      funext b'
      have hcast : (Fin.castLE (latticeRank_le W') b' : Fin k)
          = Fin.castLE (latticeRank_le W) (Fin.cast hr.symm b') := by
        apply Fin.ext
        rfl
      rw [hcast, hs]
    rw [h1, ← h2, hp]
  have hQ : ∀ σ : Fin (latticeRank W) → Fin k,
      plucker (fun a => intToRat (latticeBasis W a)) σ
        = plucker (fun a => intToRat (latticeBasis W' a)) fun b => σ (Fin.cast hr.symm b) := by
    intro σ
    rw [plucker_intToRat, plucker_intToRat, hZ σ]
  have hspan := span_eq_of_plucker_eq (latticeBasis_linearIndependent W)
    (latticeBasis_linearIndependent W') hr hQ
  rwa [latticeBasis_span, latticeBasis_span] at hspan

/-! ### Boundedness of the encoding -/

/-- The Plücker vector of a basis is controlled by the wedge norm of its image under `A`, with a
constant depending only on `A⁻¹` and `k`. -/
theorem abs_padPlucker_le (hk : 0 < k) {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsUnit A.det)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i l, |A⁻¹ i l| ≤ M) (W : Submodule ℚ (Fin k → ℚ))
    (σ : Fin k → Fin k) :
    |((padPlucker W σ : ℤ) : ℝ)| ≤ (max 1 ((k : ℝ) * M)) ^ k * latticeWedgeNorm A W := by
  haveI : NeZero k := ⟨hk.ne'⟩
  set j := latticeRank W with hj
  set B : Fin j → (Fin k → ℤ) := latticeBasis W with hB
  set σ' : Fin j → Fin k := fun b => σ (Fin.castLE (latticeRank_le W) b) with hσ'
  -- recover `B` from `A ∘ B`
  have hinv : ∀ a, intToReal (B a) = A⁻¹.mulVec (A.mulVec (intToReal (B a))) := by
    intro a
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
  have hstep : wedgeNorm (fun a => intToReal (B a))
      ≤ (k : ℝ) ^ j * M ^ j * latticeWedgeNorm A W := by
    have hrw : (fun a => intToReal (B a))
        = fun a => A⁻¹.mulVec (A.mulVec (intToReal (B a))) := funext hinv
    rw [hrw]
    exact wedgeNorm_mulVec_le hM hM0 _
  have hle1 : |((padPlucker W σ : ℤ) : ℝ)| ≤ wedgeNorm (fun a => intToReal (B a)) := by
    rw [padPlucker, ← hB, ← hσ', ← plucker_intToReal]
    exact le_wedgeNorm _ σ'
  have hconst : (k : ℝ) ^ j * M ^ j ≤ (max 1 ((k : ℝ) * M)) ^ k := by
    have hjk : j ≤ k := latticeRank_le W
    have h1 : (k : ℝ) ^ j * M ^ j = ((k : ℝ) * M) ^ j := by rw [mul_pow]
    rw [h1]
    rcases le_or_gt ((k : ℝ) * M) 1 with hcase | hcase
    · calc ((k : ℝ) * M) ^ j ≤ 1 ^ j := by
            refine pow_le_pow_left₀ (by positivity) hcase j
        _ = 1 := one_pow j
        _ ≤ (max 1 ((k : ℝ) * M)) ^ k := one_le_pow₀ (le_max_left _ _)
    · calc ((k : ℝ) * M) ^ j ≤ ((k : ℝ) * M) ^ k :=
            pow_le_pow_right₀ hcase.le hjk
        _ ≤ (max 1 ((k : ℝ) * M)) ^ k :=
            pow_le_pow_left₀ (by positivity) (le_max_right _ _) k
  have hwn : 0 ≤ latticeWedgeNorm A W := wedgeNorm_nonneg _
  calc |((padPlucker W σ : ℤ) : ℝ)| ≤ wedgeNorm (fun a => intToReal (B a)) := hle1
    _ ≤ (k : ℝ) ^ j * M ^ j * latticeWedgeNorm A W := hstep
    _ ≤ (max 1 ((k : ℝ) * M)) ^ k * latticeWedgeNorm A W :=
        mul_le_mul_of_nonneg_right hconst hwn

/-! ### Condition (A3) -/

/-- **Condition (A3).**  Only finitely many rational subspaces have short lattices. -/
theorem finite_latticeWedgeNorm_lt (hk : 0 < k) {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsUnit A.det)
    (ρ : ℝ) : {W : Submodule ℚ (Fin k → ℚ) | latticeWedgeNorm A W < ρ}.Finite := by
  classical
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ i l, |A⁻¹ i l| ≤ M := by
    obtain ⟨M₀, hM₀⟩ := Finite.exists_le fun p : Fin k × Fin k => |A⁻¹ p.1 p.2|
    exact ⟨max 0 M₀, le_max_left _ _, fun i l => le_trans (hM₀ (i, l)) (le_max_right _ _)⟩
  set C : ℝ := (max 1 ((k : ℝ) * M)) ^ k with hC
  set N : ℤ := ⌈C * ρ⌉ with hN
  have hbound : ∀ W ∈ {W : Submodule ℚ (Fin k → ℚ) | latticeWedgeNorm A W < ρ},
      ∀ σ, |padPlucker W σ| ≤ N := by
    intro W hW σ
    have h1 := abs_padPlucker_le hk hA hM0 hM W σ
    have hCpos : 0 < C := by
      rw [hC]
      have : (0:ℝ) < max 1 ((k : ℝ) * M) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      positivity
    have h2 : C * latticeWedgeNorm A W ≤ C * ρ :=
      mul_le_mul_of_nonneg_left (le_of_lt hW) hCpos.le
    have h3 : |((padPlucker W σ : ℤ) : ℝ)| ≤ C * ρ := le_trans h1 h2
    have h4 : ((|padPlucker W σ| : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      exact le_trans h3 (Int.le_ceil _)
    exact_mod_cast h4
  have hfin : ((Set.Iic k) ×ˢ (Set.univ.pi fun _ : Fin k → Fin k => Set.Icc (-N) N)).Finite :=
    (Set.finite_Iic k).prod (Set.Finite.pi fun _ => Set.finite_Icc _ _)
  have himg : latticeCode '' {W : Submodule ℚ (Fin k → ℚ) | latticeWedgeNorm A W < ρ}
      ⊆ (Set.Iic k) ×ˢ (Set.univ.pi fun _ : Fin k → Fin k => Set.Icc (-N) N) := by
    rintro _ ⟨W, hW, rfl⟩
    exact ⟨latticeRank_le W, fun σ _ => abs_le.mp (hbound W hW σ)⟩
  exact Set.Finite.of_finite_image (hfin.subset himg)
    (fun W _ W' _ hcode => latticeCode_injective hk hcode)

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
