import GaloisForLFunctions.CollectiveDiophantineGeometry.FiniteOrthogonalChartsForRealNormals
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Pigeonhole

/-!
# Optimal size of an integral similarity menu

In dimension n+1, exactly nk+1 rows suffice to separate k arbitrary nonzero
normals. They can all be first rows of integer Householder similarities.
Sampling the moment curve at multiples of one large odd prime makes every
maximal minor nonsingular by a Vandermonde reduction. Conversely, each
block of n arbitrary rows admits a common nonzero annihilator.
-/

noncomputable section
open Matrix Finset
namespace GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart

/-- Remove the column factor p^j from the Householder rows at multiples of p. -/
private def reducedRow (n p t : ℕ) (j : Fin (n+1)) : ℤ :=
  if j=0 then menuRow n (p*t) 0 else -2*(t : ℤ)^(j : ℕ)

private theorem restore_column (n p t : ℕ) (j : Fin (n+1)) :
    menuRow n (p*t) j = reducedRow n p t j * (p : ℤ)^(j : ℕ) := by
  by_cases hj : j=0
  · subst j
    simp [reducedRow]
  · simp only [menuRow_apply,reducedRow,if_neg hj,mul_zero,zero_sub]
    push_cast
    rw [mul_pow]
    ring

private theorem residue_column (n p t : ℕ) (j : Fin (n+1)) :
    (reducedRow n p t j : ZMod p) =
      (t : ZMod p)^(j : ℕ)*(if j=0 then -1 else -2) := by
  by_cases hj : j=0
  · subst j
    rw [reducedRow,if_pos rfl,menuRow_apply,Fin.sum_univ_succ]
    push_cast
    simp [Fin.val_succ,two_mul,pow_add,pow_succ]
    ring
  · simp [reducedRow,hj,mul_comm]

/-- Every n+1 distinct indices below p give independent integral rows,
including on base change to the reals. -/
theorem minor_ne_zero {n p s : ℕ} (hp : Nat.Prime p) (hp₂ : 2<p) (hs : s≤p)
    (b : Fin (n+1) ↪ Fin s) :
    (of fun i j => (menuRow n (p*(b i).val) j : ℝ)).det ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ := of fun i j => reducedRow n p (b i).val j
  let x (i : Fin (n+1)) : ZMod p := (b i).val
  have hx : Function.Injective x := by
    intro i j h
    apply b.injective
    apply Fin.val_injective
    simpa only [x,ZMod.val_natCast_of_lt ((b i).isLt.trans_le hs),
      ZMod.val_natCast_of_lt ((b j).isLt.trans_le hs)] using congrArg ZMod.val h
  let c (j : Fin (n+1)) : ZMod p := if j=0 then -1 else -2
  have hred : (Int.castRingHom (ZMod p)).mapMatrix A = vandermonde x * diagonal c := by
    ext i j
    rw [mul_diagonal,vandermonde_apply]
    exact residue_column n p (b i).val j
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    exact fun h => hp₂.not_ge (Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).1 h))
  have hD : A.det ≠ 0 := by
    intro h
    have hm : (Int.castRingHom (ZMod p)) A.det = 0 := by rw [h,map_zero]
    rw [RingHom.map_det,hred,det_mul,det_diagonal] at hm
    exact (mul_ne_zero (det_vandermonde_ne_zero_iff.mpr hx)
      (prod_ne_zero_iff.mpr fun j _ => by by_cases h : j=0 <;> simp [c,h,htwo])) hm
  let d (j : Fin (n+1)) : ℝ := (p : ℝ)^(j : ℕ)
  have he : (of fun i j => (menuRow n (p*(b i).val) j : ℝ)) =
      (Int.castRingHom ℝ).mapMatrix A * diagonal d := by
    ext i j
    rw [mul_diagonal,of_apply,restore_column,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
    rfl
  rw [he,det_mul,← RingHom.map_det,det_diagonal]
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact mul_ne_zero (by change (A.det : ℝ) ≠ 0; exact_mod_cast hD) (prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ hp')

/-- The optimal menu works simultaneously for every list of k real normals. -/
theorem prime_grid_menu {k n s p : ℕ} (hp : Nat.Prime p) (hp₂ : 2<p) (hs : s≤p)
    (hcount : k*n<s) (v : Fin k → Fin (n+1) → ℝ) (hv : ∀ a, v a ≠ 0) :
    ∃ t : Fin s, ∀ a, (fun j => (menuRow n (p*t.val) j : ℝ)) ⬝ᵥ v a ≠ 0 := by
  classical
  by_contra! hall
  choose bad hbad using hall
  obtain ⟨a,ha⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card bad
    (by simpa only [Fintype.card_fin] using hcount)
  let T := univ.filter fun t : Fin s => bad t=a
  obtain ⟨f⟩ : Nonempty (Fin (n+1) ↪ T) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin,Fintype.card_coe,T] using Nat.succ_le_of_lt ha)
  let b := f.trans (Function.Embedding.subtype fun t => t ∈ T)
  apply hv a
  apply Matrix.eq_zero_of_mulVec_eq_zero (minor_ne_zero hp hp₂ hs b)
  funext i
  have h : bad (b i) = a := (mem_filter.mp (f i).property).2
  exact h ▸ hbad (b i)

private theorem annihilating_normal {n : ℕ} (A : Matrix (Fin n) (Fin (n+1)) ℝ) :
    ∃ v : Fin (n+1) → ℝ, v ≠ 0 ∧ A *ᵥ v = 0 := by
  have hh : ¬Function.Injective A.mulVecLin := by
    intro hinj
    have h := A.mulVecLin.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_pi,Fintype.card_fin] at h
    omega
  unfold Function.Injective at hh
  push Not at hh
  obtain ⟨x,y,hxy,hne⟩ := hh
  refine ⟨x-y,sub_ne_zero.mpr hne,?_⟩
  change A.mulVecLin (x-y)=0
  rw [map_sub,hxy,sub_self]

/-- Every menu of at most nk arbitrary real rows can be covered by k
homogeneous hyperplanes. No choice of chart transformation can improve
the cardinality of the prime-grid menu. -/
theorem obstruction {k n s : ℕ} (hs : s≤k*n) (r : Fin s → Fin (n+1) → ℝ) :
    ∃ v : Fin k → Fin (n+1) → ℝ, (∀ a, v a ≠ 0) ∧
      ∀ t, ∃ a, r t ⬝ᵥ v a = 0 := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin s ↪ Fin k × Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hs)
  let rows := Function.extend e r (fun _ => 0)
  let A (a : Fin k) : Matrix (Fin n) (Fin (n+1)) ℝ := of fun i => rows (a,i)
  choose v hv hzero using fun a => annihilating_normal (A a)
  refine ⟨v,hv,fun t => ⟨(e t).1,?_⟩⟩
  have h := congrFun (hzero (e t).1) (e t).2
  change rows (e t) ⬝ᵥ v (e t).1 = 0 at h
  simpa only [rows,e.injective.extend_apply] using h

/-- Exact minimum even when all rows must come from the same integral
Householder family, with indices independent of the normals. -/
theorem menu_size_iff (n k s : ℕ) :
    (∃ t : Fin s → ℕ, ∀ v : Fin k → Fin (n+1) → ℝ, (∀ a, v a ≠ 0) →
      ∃ i, ∀ a, (fun j => (menuRow n (t i) j : ℝ)) ⬝ᵥ v a ≠ 0) ↔ k*n<s := by
  constructor
  · rintro ⟨t,ht⟩
    by_contra! h
    obtain ⟨v,hv,hbad⟩ := obstruction h (fun i j => (menuRow n (t i) j : ℝ))
    obtain ⟨i,hi⟩ := ht v hv
    obtain ⟨a,ha⟩ := hbad i
    exact hi a ha
  · intro h
    obtain ⟨p,hle,hp⟩ := Nat.exists_infinite_primes (max s 3)
    exact ⟨fun i => p*i.val,fun v hv => prime_grid_menu hp (by omega)
      ((le_max_left _ _).trans hle) h v hv⟩

end GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart

#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart.minor_ne_zero
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart.prime_grid_menu
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart.obstruction
#print axioms GaloisForLFunctions.CollectiveDiophantineGeometry.FrameChart.menu_size_iff
