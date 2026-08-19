import GaloisForLFunctions.HTGeometry.OpenSiegelSet

/-!
# Matrices over an order, read as integral block matrices

A ring free of rank `d` over `ℤ` acts on itself by multiplication, and a choice of `ℤ`-basis turns
that action into a `d × d` integral matrix.  Applying this entrywise to an `n × n` matrix over the
ring and flattening the four indices gives an `nd × nd` integral matrix, multiplicatively and
injectively.  So `GL_n(R)` sits inside `GL_{nd}(ℤ)`, which is what puts the reduction theory of the
integral cone at the disposal of matrices over an order.

* `blockEmbed` : the flattening.
* `blockEmbed_one`, `blockEmbed_mul`, `blockEmbed_injective` : it is an injective monoid map.
* `orderRep` : the composite with the regular representation.
* `isIntUnimodular_orderRep` : **units of `M_n(R)` give integral unimodular matrices.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {nb d : ℕ}

theorem val_finProdFinEquiv (j : Fin nb) (l : Fin d) :
    ((finProdFinEquiv (j, l) : Fin (nb * d)) : ℕ) = (l : ℕ) + d * (j : ℕ) := by
  simp [finProdFinEquiv]

theorem divNat_finProdFinEquiv (j : Fin nb) (l : Fin d) :
    Fin.divNat (finProdFinEquiv (j, l)) = j := by
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) l.isLt
  refine Fin.ext ?_
  show ((finProdFinEquiv (j, l) : Fin (nb * d)) : ℕ) / d = (j : ℕ)
  rw [val_finProdFinEquiv, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt l.isLt, Nat.zero_add]

theorem modNat_finProdFinEquiv (j : Fin nb) (l : Fin d) :
    Fin.modNat (finProdFinEquiv (j, l)) = l := by
  refine Fin.ext ?_
  show ((finProdFinEquiv (j, l) : Fin (nb * d)) : ℕ) % d = (l : ℕ)
  rw [val_finProdFinEquiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l.isLt]

theorem finProdFinEquiv_divNat_modNat (p : Fin (nb * d)) :
    finProdFinEquiv (Fin.divNat p, Fin.modNat p) = p := by
  have hpos : 0 < nb * d := lt_of_le_of_lt (Nat.zero_le _) p.isLt
  have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at hpos
    omega
  refine Fin.ext ?_
  rw [val_finProdFinEquiv]
  show (p : ℕ) % d + d * ((p : ℕ) / d) = (p : ℕ)
  exact Nat.mod_add_div _ _

/-- The flattening of a matrix of matrices. -/
def blockEmbed {S : Type*} (M : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) S)) :
    Matrix (Fin (nb * d)) (Fin (nb * d)) S :=
  Matrix.of fun p q => M (Fin.divNat p) (Fin.divNat q) (Fin.modNat p) (Fin.modNat q)

theorem blockEmbed_apply' {S : Type*} (M : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) S))
    (p q : Fin (nb * d)) :
    blockEmbed M p q = M (Fin.divNat p) (Fin.divNat q) (Fin.modNat p) (Fin.modNat q) := rfl

@[simp]
theorem blockEmbed_apply {S : Type*} (M : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) S))
    (i j : Fin nb) (k l : Fin d) :
    blockEmbed M (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) = M i j k l := by
  rw [blockEmbed_apply', divNat_finProdFinEquiv, divNat_finProdFinEquiv, modNat_finProdFinEquiv,
    modNat_finProdFinEquiv]

theorem blockEmbed_one {S : Type*} [Semiring S] :
    blockEmbed (1 : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) S)) = 1 := by
  classical
  ext p q
  rw [blockEmbed_apply']
  by_cases hpq : p = q
  · subst hpq
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hpq]
    by_cases hdiv : (Fin.divNat p : Fin nb) = Fin.divNat q
    · rw [hdiv, Matrix.one_apply_eq]
      refine Matrix.one_apply_ne ?_
      intro hmod
      refine hpq ?_
      rw [← finProdFinEquiv_divNat_modNat p, ← finProdFinEquiv_divNat_modNat q, hdiv, hmod]
    · rw [Matrix.one_apply_ne hdiv, Matrix.zero_apply]

theorem blockEmbed_mul {S : Type*} [Semiring S]
    (M N : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) S)) :
    blockEmbed (M * N) = blockEmbed M * blockEmbed N := by
  classical
  ext p q
  rw [blockEmbed_apply', Matrix.mul_apply, Matrix.mul_apply]
  have hsum : (∑ r : Fin (nb * d), blockEmbed M p r * blockEmbed N r q)
      = ∑ x : Fin nb × Fin d,
        M (Fin.divNat p) x.1 (Fin.modNat p) x.2 * N x.1 (Fin.divNat q) x.2 (Fin.modNat q) := by
    rw [← Equiv.sum_comp (finProdFinEquiv (m := nb) (n := d))
      (fun r : Fin (nb * d) => blockEmbed M p r * blockEmbed N r q)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [blockEmbed_apply', blockEmbed_apply', divNat_finProdFinEquiv, modNat_finProdFinEquiv]
  rw [hsum, Fintype.sum_prod_type, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun j _ => Matrix.mul_apply

theorem blockEmbed_injective {S : Type*} :
    Function.Injective (blockEmbed (nb := nb) (d := d) (S := S)) := by
  intro M N hMN
  ext i j k l
  have h := congrFun (congrFun hMN (finProdFinEquiv (i, k))) (finProdFinEquiv (j, l))
  rwa [blockEmbed_apply, blockEmbed_apply] at h

variable {R : Type*} [CommRing R]

/-- Matrices over an order, read as integral matrices through the regular representation. -/
noncomputable def orderRep (ω : Module.Basis (Fin d) ℤ R)
    (M : Matrix (Fin nb) (Fin nb) R) : Matrix (Fin (nb * d)) (Fin (nb * d)) ℤ :=
  blockEmbed (M.map (Algebra.leftMulMatrix ω))

theorem orderRep_one (ω : Module.Basis (Fin d) ℤ R) :
    orderRep (nb := nb) ω 1 = 1 := by
  have hmap : ((1 : Matrix (Fin nb) (Fin nb) R).map (Algebra.leftMulMatrix ω))
      = (1 : Matrix (Fin nb) (Fin nb) (Matrix (Fin d) (Fin d) ℤ)) :=
    map_one ((Algebra.leftMulMatrix ω).toRingHom.mapMatrix)
  rw [orderRep, hmap, blockEmbed_one]

theorem orderRep_mul (ω : Module.Basis (Fin d) ℤ R) (M N : Matrix (Fin nb) (Fin nb) R) :
    orderRep ω (M * N) = orderRep ω M * orderRep ω N := by
  have hmap : ((M * N).map (Algebra.leftMulMatrix ω))
      = (M.map (Algebra.leftMulMatrix ω)) * (N.map (Algebra.leftMulMatrix ω)) :=
    map_mul ((Algebra.leftMulMatrix ω).toRingHom.mapMatrix) M N
  rw [orderRep, hmap, blockEmbed_mul, orderRep, orderRep]

/-- The regular representation as a monoid map. -/
noncomputable def orderRepHom (ω : Module.Basis (Fin d) ℤ R) :
    Matrix (Fin nb) (Fin nb) R →* Matrix (Fin (nb * d)) (Fin (nb * d)) ℤ where
  toFun := orderRep ω
  map_one' := orderRep_one ω
  map_mul' := orderRep_mul ω

theorem orderRep_injective (ω : Module.Basis (Fin d) ℤ R) :
    Function.Injective (orderRep (nb := nb) ω) := by
  intro M N hMN
  have h := blockEmbed_injective hMN
  ext i j
  refine Algebra.leftMulMatrix_injective ω ?_
  exact congrFun (congrFun h i) j

/-- **A unit of `M_n(R)` gives an integral unimodular matrix.** -/
theorem isIntUnimodular_orderRep (ω : Module.Basis (Fin d) ℤ R)
    {M : Matrix (Fin nb) (Fin nb) R} (hM : IsUnit M) :
    IsIntUnimodular ((orderRep ω M).map (fun z : ℤ => (z : ℝ))) :=
  ⟨orderRep ω M, hM.map (orderRepHom ω), fun _ _ => rfl⟩

end GaloisForLFunctions.HTGeometry
