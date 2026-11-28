import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicRadicalContraction
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSplitCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraCuspidalRestriction
import Mathlib.RepresentationTheory.Coinvariants

/-! A nonconstant diagonal torus translate of an inflated cuspidal
type vanishes in first principal-congruence coinvariants. Conjugation
contracts a proper radical, whose finite average is zero. -/

noncomputable section

open Matrix GlobalTheory.GLq Representation

namespace GlobalTheory.GLp

variable {p m : ℕ} [Fact p.Prime] {V W : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

private abbrev leviKernel (p a b : ℕ) [Fact p.Prime] :=
  (twoBlockLevi (g := p) (a := a) (b := b)).ker

private abbrev leviKernelFintype (p a b : ℕ) [Fact p.Prime] : Fintype (leviKernel p a b) :=
  Fintype.ofFinite (leviKernel p a b)

private theorem sum_reindexed_radical_action_eq_zero {a b : ℕ}
    (τ : Representation ℂ (Gn p m) W) (hτ : IsCusp τ.character)
    (ha : 0 < a) (hb : 0 < b) (e : Fin (a + b) ≃ Fin m) :
    letI := leviKernelFintype p a b
    ∑ u : leviKernel p a b, τ (reindexUnit e u.val.val) = 0 := by
  have hm : a + b = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  letI := leviKernelFintype p a b
  let w : Gn p (a + b) := monomialUnit e (fun _ => 1)
  have hform (u : leviKernel p a b) : τ (reindexUnit e u.val.val) = τ w * τ u.val.val * τ w⁻¹ := by
    rw [reindexUnit_perm, ← map_mul, ← map_mul]
  have hab : a + b - a = b := by omega
  have hres : res a b τ.character 1 1 = 0 := by
    let D (c : ℕ) : Prop := res a c τ.character 1 1 = 0
    exact (congrArg D hab).mp (hτ.2.2 a ha (show a < a + b by omega))
  have hsum := sum_leviKernel_eq_zero_of_degree_zero τ hres
  simp only [hform, ← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_zero, zero_mul]

theorem torus_cuspidal_mem_principal_coinvariantKer
    (ρ : Representation ℂ (GL (Fin m) ℚ_[p]) V)
    (τ : Representation ℂ (Gn p m) W) (hτ : IsCusp τ.character)
    (j : W →ₗ[ℂ] V)
    (hj : ∀ (k : GL (Fin m) ℤ_[p]) (w : W),
      j (τ (integralReduction p (Fin m) k) w) = ρ (integralInclusion p (Fin m) k) (j w))
    (a : Fin m → ℤ) (ha : ∃ i l, a i ≠ a l) (w : W) :
    ρ (uniformizerTorus (p := p) a) (j w) ∈
      Coinvariants.ker (ρ.comp (principalCongruenceOne p (Fin m)).subtype) := by
  classical
  obtain ⟨i, l, hil⟩ := ha
  let s (k : Fin m) := ∀ x, a x ≤ a k
  have hs : ∃ k, s k := by
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ a ⟨i, Finset.mem_univ _⟩
    exact ⟨k, fun x => hk x (Finset.mem_univ _)⟩
  have ht : ∃ k, ¬ s k := by
    rcases lt_or_gt_of_ne hil with h | h
    · exact ⟨i, fun hi => h.not_ge (hi l)⟩
    · exact ⟨l, fun hl => h.not_ge (hl i)⟩
  have hlt (i j : Fin m) (hi : s i) (hj' : ¬ s j) : a j < a i := by
    obtain ⟨k, hk⟩ := not_forall.mp hj'
    exact (lt_of_not_ge hk).trans_le (hi k)
  obtain ⟨b, c, hb, hc, e, he⟩ := exists_fin_split s hs ht
  let N := leviKernel p b c
  letI := leviKernelFintype p b c
  let K := principalCongruenceOne p (Fin m)
  let r : Representation ℂ K V := ρ.comp K.subtype
  let t := uniformizerTorus (p := p) a
  let x := ρ t (j w)
  let f (u : N) := ρ t (j (τ (reindexUnit e u.val.val) w))
  have hterm (u : N) : x - f u ∈ Coinvariants.ker r := by
    let v := reindexUnit e u.val.val
    have hv (i j : Fin m) (h : ¬ (s i ∧ ¬ s j)) : (v.val - 1) i j = 0 := by
      rw [Matrix.sub_apply, reindexedRadical_apply_eq_one_of_not_cross e he u i j h, sub_self]
    obtain ⟨k, hk, hk'⟩ := exists_integral_radical_lift_contracted s a hlt v hv
    let g := integralInclusion p (Fin m) k
    let vK : K := ⟨t * g * t⁻¹, hk'⟩
    have heq : f u = r vK x := by
      change ρ t (j (τ v w)) = ρ (t * g * t⁻¹) (ρ t (j w))
      rw [← hk, hj, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel_right]
    rw [heq, ← neg_sub]
    exact (Coinvariants.ker r).neg_mem (Coinvariants.sub_mem_ker vK x)
  have hzero : ∑ u : N, f u = 0 := by
    have h := sum_reindexed_radical_action_eq_zero τ hτ hb hc e
    change ∑ u : N, ρ t (j (τ (reindexUnit e u.val.val) w)) = 0
    rw [← map_sum, ← map_sum, ← LinearMap.sum_apply, h, LinearMap.zero_apply, map_zero, map_zero]
  have hmem := Submodule.sum_mem (Coinvariants.ker r) fun u (_ : u ∈ Finset.univ) => hterm u
  rw [Finset.sum_sub_distrib, hzero, sub_zero, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ] at hmem
  have hcard : (Fintype.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (Submodule.smul_mem_iff _ hcard).mp hmem

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.torus_cuspidal_mem_principal_coinvariantKer
