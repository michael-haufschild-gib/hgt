import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechKunneth
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechTraceTensorAction

/-! A mixed cocycle acting as the identity gives a finite resolution
of the identity on each projective Čech cohomology group. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.WH
open scoped GlobalTheory.CechDR TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

private abbrev P (n : ℕ) (I : Finset (Fin (d + 1))) := omB k E (rB k E x I) n

private abbrev tensorLattice (a b : ℕ) (I J : Finset (Fin (d + 1))) :=
  Submodule.map₂ (TensorProduct.mk k (DR k E) (DR k E)) (P (x := x) a I) (P (x := x) b J)

omit [CharZero k] in
private theorem cech_apply_zero_of_degree_ne {A : Finset (Fin (d + 1)) → Submodule k (DR k E)}
    {q : ℕ} {v : Finset (Fin (d + 1)) → DR k E}
    (hv : v ∈ (cech A).Z q) (I : Finset (Fin (d + 1))) (hI : I.card ≠ q + 1) : v I = 0 := by
  have hm := (Submodule.mem_pi.mp hv.1) I (Set.mem_univ _)
  change v I ∈ (if I.Nonempty ∧ (I.card : ℤ) = (q : ℤ) + 1 then A I else ⊥) at hm
  rw [if_neg (fun h => hI (by exact_mod_cast h.2))] at hm
  exact (Submodule.mem_bot k).mp hm

omit [CharZero k] in
private theorem cupResidueFunctional_eq_zero_of_degree_ne
    (τ : DR k E →ₗ[E] E) (ρ : F →ₗ[k] k) {a b p q : ℕ} (hp : p ≤ d) (hpq : p ≠ q)
    {u v : Finset (Fin (d + 1)) → DR k E}
    (hu : u ∈ (cech (P (x := x) a)).Z ((d - p : ℕ) : ℤ))
    (hv : v ∈ (cech (P (x := x) b)).Z q) :
    cupResidueFunctional τ ρ u v = 0 := by
  rw [cupResidueFunctional_apply, cechCup_apply]
  rw [show (∑ i, LinearMap.mul k (DR k E) (u (Finset.univ.filter (· ≤ i)))
      (v (Finset.univ.filter (i ≤ ·)))) = 0 from Finset.sum_eq_zero (fun i hi => ?_), map_zero]
  by_cases hL : (Finset.univ.filter (· ≤ i)).card = d - p + 1
  · have hc := card_filter_le_add_card_filter_ge Finset.univ i hi
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    rw [cech_apply_zero_of_degree_ne hv _ (by omega), map_zero]
  · rw [cech_apply_zero_of_degree_ne hu _ hL, map_zero, LinearMap.zero_apply]

/-- A diagonal cocycle acting as the identity in cohomology decomposes
into complementary cocycles whose residue functionals resolve the identity. -/
theorem IsFinCover.cocycle_resolution_of_diagonal_action (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    {a b : ℕ} (hab : a + b = d)
    {z : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) → DR k E ⊗[k] DR k E}
    (hz : z ∈ (mixedCech (tensorLattice (x := x) a b)).Z ((d : ℤ) + 2))
    (hzid : ∀ q ≤ d, ∀ v ∈ (cech (P (x := x) b)).Z q,
      v - cupAlongLeft (traceWedgeTensorAction τ ρ) v z ∈ (cech (P (x := x) b)).B q) :
    ∃ (m : ℕ) (p : Fin m → ℕ) (e f : Fin m → Finset (Fin (d + 1)) → DR k E),
      (∀ j, p j ≤ d ∧ e j ∈ (cech (P (x := x) a)).Z ((d - p j : ℕ) : ℤ) ∧
        f j ∈ (cech (P (x := x) b)).Z (p j)) ∧
      z - ∑ j, cechJoin (TensorProduct.mk k (DR k E) (DR k E)) (e j) (f j) ∈
        (mixedCech (tensorLattice (x := x) a b)).B ((d : ℤ) + 2) ∧
      ∀ q : ℕ, ∀ v ∈ (cech (P (x := x) b)).Z q,
        v - ∑ j ∈ Finset.univ.filter (fun j => p j = q), cupResidueFunctional τ ρ (e j) v • f j ∈
          (cech (P (x := x) b)).B q := by
  have hmono (n : ℕ) (I J : Finset (Fin (d + 1))) (_ : I.Nonempty) (hIJ : I ⊆ J) :
      P (E := E) (x := x) (k := k) n I ≤ P (x := x) n J :=
    omB_mono (rB_mono (E := E) (x := x) hIJ) n
  obtain ⟨m, p, e, f, hparts, hzb⟩ := mixedCech_kunneth (P (x := x) a) (P (x := x) b) (hmono a) (hmono b) d hz
  refine ⟨m, p, e, f, hparts, hzb, ?_⟩
  intro q v hv
  by_cases hq : q ≤ d
  · let μ := traceWedgeTensorAction τ ρ
    let T (j : Fin m) := cechJoin (TensorProduct.mk k (DR k E) (DR k E)) (e j) (f j)
    have hsum :
        cupAlongLeft μ v (z - ∑ j, T j) =
          cupAlongLeft μ v z - ∑ j ∈ Finset.univ.filter (fun j => p j = q),
            cupResidueFunctional τ ρ (e j) v • f j := by
      have hzero (j : Fin m) (hj : p j ≠ q) : cupResidueFunctional τ ρ (e j) v = 0 :=
        cupResidueFunctional_eq_zero_of_degree_ne τ ρ (hparts j).1 hj (hparts j).2.1 hv
      rw [Finset.sum_filter_of_ne (fun j _ hj => ?_)]
      · funext J
        simp only [cupAlongLeft, cechCup_apply, Pi.sub_apply, Finset.sum_apply, map_sub,
          LinearMap.sub_apply, Finset.sum_sub_distrib, map_sum, LinearMap.sum_apply]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [T, μ, cechJoin, lft_uni, rgt_uni, TensorProduct.mk_apply,
          traceWedgeTensorAction_tmul, Pi.smul_apply, cupResidueFunctional_apply,
          cechCup_apply, map_sum, Finset.sum_smul, LinearMap.mul_apply']
      · by_contra hneq
        exact hj (by rw [hzero j hneq, zero_smul])
    have hb := h.traceWedgeTensorAction_boundary τ hτ ρ hρ hab hq hv hzb
    change cupAlongLeft μ v (z - ∑ j, T j) ∈ _ at hb
    rw [hsum] at hb
    have hid := hzid q hq v hv
    convert add_mem hid hb using 1
    abel
  · have hv₀ : v = 0 := funext fun I => cech_apply_zero_of_degree_ne hv I (by
      have hi := Finset.card_le_univ I
      simp only [Fintype.card_fin] at hi
      omega)
    rw [hv₀]
    simp

end GlobalTheory.PD
