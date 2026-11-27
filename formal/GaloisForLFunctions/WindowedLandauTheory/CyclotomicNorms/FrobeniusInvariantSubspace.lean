import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.SquarefreeFrobeniusCycles
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.SeparatedInertiaLines

/-! With distinct inertia eigenvalues, invariant subspaces are sums of
eigenlines. Frobenius invariance makes their index sets give divisors over
the prime field, of degree equal to the subspace dimension. -/

noncomputable section

open Module Polynomial Matrix

namespace WindowedLandauTheory.CyclotomicNorms.CycleTypeFiniteOrder

variable {k : Type} [Field k] {N : ℕ}

/-- The standard linear action of the matrix group. -/
def repGL : GL (Fin N) k →* Module.End k (Fin N → k) :=
  Matrix.toLinAlgEquiv'.toAlgHom.toMonoidHom.comp (Units.coeHom _)

theorem repGL_apply (A : GL (Fin N) k) (x : Fin N → k) :
    repGL A x = (A : Matrix (Fin N) (Fin N) k) *ᵥ x :=
  Matrix.toLin'_apply _ _

theorem repGL_injective : Function.Injective (repGL (k := k) (N := N)) := fun _ _ h =>
  Units.ext (Matrix.toLin'.injective h)

theorem charpoly_repGL (A : GL (Fin N) k) :
    (repGL A).charpoly = (A : Matrix (Fin N) (Fin N) k).charpoly :=
  Matrix.charpoly_toLin' _

private theorem repGL_injective_apply (A : GL (Fin N) k) : Function.Injective (repGL A) := by
  apply Function.LeftInverse.injective (g := repGL A⁻¹)
  intro x
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- Distinct roots of the characteristic polynomial give an eigenbasis. -/
theorem exists_eigenbasis_of_roots (A : GL (Fin N) k) (L : Fin N → k) (hL : Function.Injective L)
    (hroots : (A : Matrix (Fin N) (Fin N) k).charpoly.roots = Finset.univ.val.map L) :
    ∃ e : Module.Basis (Fin N) k (Fin N → k), ∀ i, (repGL A).HasEigenvector (L i) (e i) := by
  have he (i : Fin N) : (repGL A).HasEigenvalue (L i) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, charpoly_repGL]
    apply (mem_roots (Matrix.charpoly_monic _).ne_zero).mp
    rw [hroots]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  choose w hw using fun i => (he i).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent' (repGL A) L hL w hw
  let e : Module.Basis (Fin N) k (Fin N → k) :=
    basisOfLinearIndependentOfCardEqFinrank' w hli (by rw [Module.finrank_fintype_fun_eq_card])
  exact ⟨e, fun i => by simpa only [e, coe_basisOfLinearIndependentOfCardEqFinrank'] using hw i⟩

/-- A subspace invariant under inertia and inverse Frobenius has the dimension
of a monic prime-field divisor of the original squarefree polynomial. -/
theorem exists_divisor_finrank_of_invariant {g : ℕ} [Fact g.Prime] {f : (ZMod g)[X]}
    (hf : GoodPoly N f) (r : Fin N → Fbar g) (σ : Equiv.Perm (Fin N))
    (hrf : Finset.univ.val.map r = rootsBar f) (hσ : ∀ i, r (σ i) = r i ^ g)
    (A B : GL (Fin N) k) (L : Fin N → k) (hL : Function.Injective L)
    (hLσ : ∀ i, L (σ i) = L i ^ g) (hconj : B * A * B⁻¹ = A ^ g)
    (hroots : (A : Matrix (Fin N) (Fin N) k).charpoly.roots = Finset.univ.val.map L)
    (W : Submodule k (Fin N → k))
    (hA : ∀ x ∈ W, repGL A x ∈ W) (hB : ∀ x ∈ W, repGL B⁻¹ x ∈ W) :
    ∃ Q : (ZMod g)[X], Q.Monic ∧ Q ∣ f ∧ Q.natDegree = Module.finrank k W := by
  obtain ⟨e, he⟩ := exists_eigenbasis_of_roots A L hL hroots
  let T : Unit → Module.End k (Fin N → k) := fun _ => repGL A
  let values : Fin N → Unit → k := fun i _ => L i
  have hdiag (i : Fin N) (u : Unit) : T u (e i) = values i u • e i := by
    simpa only [T, values, pow_one] using (he i).pow_apply 1
  have hsep (i j : Fin N) (hij : i ≠ j) : ∃ u : Unit, values i u ≠ values j u := ⟨(), fun h => hij (hL h)⟩
  have hcoord := mem_of_repr_ne_zero T e values hdiag hsep W (fun _ => hA)
  let S := basisIndices e W
  have hdim : Module.finrank k W = S.card := finrank_eq_card_basisIndices e W hcoord
  have hcomm : repGL A * repGL B⁻¹ = repGL B⁻¹ * repGL A ^ g := by
    rw [← map_pow, ← map_mul, ← map_mul, ← hconj]
    congr 1
    group
  have hS (i : Fin N) (hi : i ∈ S) : σ i ∈ S := by
    have hvec : repGL A (repGL B⁻¹ (e i)) = L (σ i) • repGL B⁻¹ (e i) := by
      rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply, (he i).pow_apply, map_smul, hLσ]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (eigen_mem_span T e values hdiag hsep (σ i) (repGL B⁻¹ (e i)) (fun _ => hvec))
    have hn : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      apply e.ne_zero i
      exact repGL_injective_apply B⁻¹ (by rw [← hc, map_zero])
    have hmem := W.smul_mem c⁻¹ (hB _ ((mem_basisIndices e W i).mp hi))
    rw [← hc, smul_smul, inv_mul_cancel₀ hn, one_smul] at hmem
    exact (mem_basisIndices e W (σ i)).mpr hmem
  obtain ⟨Q, hm, hQ, hdeg, -⟩ := exists_dvd hf hrf hσ S hS
  exact ⟨Q, hm, hQ, hdeg.trans hdim.symm⟩


/-- If no degree in the lower half occurs as a divisor of every label,
the representation with these inertia and Frobenius actions is irreducible. -/
theorem irredOn_of_indexed_labels {g ℓ : ℕ} [Fact g.Prime] [Fact ℓ.Prime]
    {P Γ : Type} [Group Γ] {f : P → (ZMod g)[X]} (hf : ∀ v, GoodPoly N (f v))
    (havoid : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ Q : (ZMod g)[X], Q ∣ f v ∧ Q.natDegree = a)
    (r : P → Fin N → Fbar g) (σ : P → Equiv.Perm (Fin N))
    (hr : ∀ v, Finset.univ.val.map (r v) = rootsBar (f v))
    (hσ : ∀ v j, r v (σ v j) = r v j ^ g)
    (L : P → Fin N → Fbar ℓ) (hinj : ∀ v, Function.Injective (L v))
    (hL : ∀ v j, L v (σ v j) = L v j ^ g)
    (ρ : Γ →* GL (Fin N) (Fbar ℓ)) (τ φ : P → Γ)
    (hφ : ∀ v, ρ (φ v * τ v * (φ v)⁻¹) = ρ (τ v) ^ g)
    (hτ : ∀ v, (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly.roots =
      Finset.univ.val.map (L v)) : IrredOn ρ ⊤ := by
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  by_contra htop
  let d := Module.finrank (Fbar ℓ) W
  have hpos : 0 < d := by
    have h := Submodule.finrank_strictMono (K := Fbar ℓ) (bot_lt_iff_ne_bot.mpr hbot)
    simpa only [finrank_bot] using h
  have hlt : d < N := by
    have h := Submodule.finrank_strictMono (K := Fbar ℓ) (lt_top_iff_ne_top.mpr htop)
    simpa only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using h
  let a := min d (N - d)
  have ha : 1 ≤ a := by dsimp [a]; omega
  have ha₂ : 2 * a ≤ N := by dsimp [a]; omega
  obtain ⟨v, hv⟩ := havoid a ha ha₂
  apply hv
  have hconj : ρ (φ v) * ρ (τ v) * (ρ (φ v))⁻¹ = ρ (τ v) ^ g := by
    simpa only [map_mul, map_inv] using hφ v
  obtain ⟨Q, hQm, hQ, hd⟩ := exists_divisor_finrank_of_invariant (hf v) (r v) (σ v)
    (hr v) (hσ v) (ρ (τ v)) (ρ (φ v)) (L v) (hinj v) (hL v) hconj (hτ v) W
    (fun x hx => by rw [repGL_apply]; exact hW _ (Subgroup.mem_top _) x hx)
    (fun x hx => by rw [← map_inv, repGL_apply]; exact hW _ (Subgroup.mem_top _) x hx)
  by_cases hsmall : d ≤ N - d
  · exact ⟨Q, hQ, by simpa only [a, min_eq_left hsmall] using hd⟩
  · obtain ⟨Q', hQ'⟩ := hQ
    have hQ'₀ : Q' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hQ'
      exact (hf v).monic.ne_zero hQ'
    have hsum : N = d + Q'.natDegree := by
      rw [← (hf v).deg, hQ', hQm.natDegree_mul' hQ'₀, hd]
    refine ⟨Q', ⟨Q, by rw [hQ', mul_comm]⟩, ?_⟩
    dsimp [a]
    omega

/-- Root labels related by Frobenius give absolute irreducibility when their
common divisor degrees are only zero and the full dimension. -/
theorem irredOn_of_labels {g ℓ : ℕ} [Fact g.Prime] [Fact ℓ.Prime]
    {P Γ : Type} [Group Γ] {f : P → (ZMod g)[X]} (hf : ∀ v, GoodPoly N (f v))
    (havoid : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ Q : (ZMod g)[X], Q ∣ f v ∧ Q.natDegree = a)
    (a : P → Fbar g →* Fbar ℓ)
    (ha : ∀ v, ∀ x ∈ rootsBar (f v), ∀ y ∈ rootsBar (f v), a v x = a v y → x = y)
    (ρ : Γ →* GL (Fin N) (Fbar ℓ)) (τ : P → Γ)
    (hφ : ∀ v, ∃ φ, ρ (φ * τ v * φ⁻¹) = ρ (τ v) ^ g)
    (hτ : ∀ v, (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly =
      ((rootsBar (f v)).map fun x => X - C (a v x)).prod) : IrredOn ρ ⊤ := by
  choose r σ hr hrf hσ using fun v => exists_index (hf v)
  choose φ hφ using hφ
  have hmem (v : P) (j : Fin N) : r v j ∈ rootsBar (f v) := by
    rw [← hrf v]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
  refine irredOn_of_indexed_labels hf havoid r σ hrf hσ (fun v j => a v (r v j))
    (fun v j k h => hr v (ha v _ (hmem v j) _ (hmem v k) h)) (fun v j => ?_) ρ τ φ hφ (fun v => ?_)
  · rw [hσ, map_pow]
  · have hcp : (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly =
        ((Finset.univ.val.map (fun j => a v (r v j))).map fun x => X - C x).prod := by
      rw [hτ, ← hrf, Multiset.map_map, Multiset.map_map]
      rfl
    rw [hcp, roots_multiset_prod_X_sub_C]

end WindowedLandauTheory.CyclotomicNorms.CycleTypeFiniteOrder
