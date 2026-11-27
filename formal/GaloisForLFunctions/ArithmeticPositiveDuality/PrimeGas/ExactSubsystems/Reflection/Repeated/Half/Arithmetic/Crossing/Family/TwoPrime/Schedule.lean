import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime.Spectrum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse.Commensurate
import GaloisForLFunctions.HTGeometry.RationalCommonTimeWitness

/-! # Two independent prime modes defeat every finite rational schedule on simple spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime

open Finset Real
open _root_.HTGeometry (finiteGibbsStateWeight)

/-- For any prescribed pair of different primes, finitely many positive rational
orders can all be blind at unit damping on a single simple asymmetric spectrum. -/
theorem rational_schedule (p q : Nat.Primes) (diff : p ≠ q) (T : Finset ℚ) (pos : ∀ t ∈ T, 0<t) :
    ∃ (m : ℕ) (k : Fin m ↪ ℕ × ℕ), ¬Reflects (mode p q ∘ k) ∧
      ∀ t ∈ T, agrees (mode p q ∘ k) (t : ℝ) := by
  classical
  obtain ⟨D,hd,all⟩ := GaloisForLFunctions.HTGeometry.exists_common_denominator_rationalCommonTimeWitness
    (fun t : T => t.val)
  choose z eq using all
  let j (t : T) := (z t).toNat
  have scale (t : T) : (t.val : ℝ)*(D : ℝ)=(j t : ℝ) := by
    have zp : 0 < z t := by
      have h := mul_pos (Nat.cast_pos.mpr hd : (0 : ℚ)<D) (pos t.val t.property)
      rw [eq t] at h
      exact_mod_cast h
    have cast : (j t : ℝ)=(z t : ℝ) := by exact_mod_cast Int.toNat_of_nonneg zp.le
    rw [cast,mul_comm]
    exact_mod_cast eq t
  obtain ⟨n,A,B,disj,non,firsts,seconds,hits⟩ := blocks p q (univ.image j)
  let E := signedEnergy A B (source p q)
  let k := occupations D A B
  have mean := balanced_mean p q firsts seconds
  have asym : ¬Reflects E := signed_asymmetric A B _ disj non (source_pos p q) (source_injective p q diff) mean
  have d0 : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have law := realized p q A B D
  have nonreflecting : ¬Reflects (mode p q ∘ k) := by
    rw [show mode p q ∘ k=_ from law,Lattice.affine_reflects _ _ _ d0]
    exact asym
  have pass (t : T) : agrees (mode p q ∘ k) (t.val : ℝ) := by
    rw [show mode p q ∘ k=_ from law,agrees_affine,scale t]
    have h := hits (j t) (mem_image_of_mem j (mem_univ t))
    exact balanced_reading p q mean (j t) h.1 h.2
  have inj : Function.Injective k := by
    intro x y h
    have same := congrArg (mode p q) h
    change (mode p q ∘ k) x=(mode p q ∘ k) y at same
    rw [show mode p q ∘ k=_ from law] at same
    have energy := mul_left_cancel₀ d0 (add_right_cancel same)
    exact absolute_injective A B _ disj (source_pos p q) (source_injective p q diff) (congrArg abs energy)
  let e := (Fintype.equivFin (States A B)).symm
  let a : Fin (Fintype.card (States A B)) ↪ ℕ × ℕ := ⟨k ∘ e,inj.comp e.injective⟩
  have pair : Matches (mode p q ∘ a) (mode p q ∘ k) := ⟨e,fun _ => rfl⟩
  exact ⟨_,a,fun ref => nonreflecting ((reflects_congr pair).mp ref),fun t ht => (agrees_congr pair _).mpr (pass ⟨t,ht⟩)⟩

private theorem diagonal {I : Type*} (p : Nat.Primes) (k : I → ℕ × ℕ) :
    mode p p ∘ k=Lattice.primeModes p (fun i => (k i).1+(k i).2) := by
  funext i
  change log (((p.val^(k i).1*p.val^(k i).2 : ℕ) : ℝ))=log (((p.val^((k i).1+(k i).2) : ℕ) : ℝ))
  rw [pow_add]

/-- For a nonempty rational schedule, two different prime frequencies are
necessary and sufficient for a false positive with pairwise distinct energies. -/
theorem simple_schedule_iff (p q : Nat.Primes) (T : Finset ℚ) (non : T.Nonempty) (pos : ∀ t ∈ T, 0<t) :
    (∃ (m : ℕ) (k : Fin m → ℕ × ℕ), Function.Injective (mode p q ∘ k) ∧ ¬Reflects (mode p q ∘ k) ∧
      ∀ t ∈ T, agrees (mode p q ∘ k) (t : ℝ)) ↔ p≠q := by
  constructor
  · rintro ⟨m,k,inj,asym,hit⟩ rfl
    let a (i : Fin m) := (k i).1+(k i).2
    rw [diagonal] at inj asym
    have simple : Function.Injective a := by
      intro i j eq
      apply inj
      change energy ⟨p.val^a i,_⟩=energy ⟨p.val^a j,_⟩
      simp only [eq]
    obtain ⟨t,ht⟩ := non
    have h := hit t ht
    rw [diagonal] at h
    have cap (j : ℕ) := (Lattice.Sparse.simple_multiplicity simple j).trans_lt p.property.one_lt
    have alg : IsAlgebraic ℚ (t : ℝ) := isAlgebraic_algebraMap t
    have either := (Lattice.Sparse.algebraic_reading p a cap (t : ℝ) alg).mp h
    exact asym (either.resolve_left (Rat.cast_pos.mpr (pos t ht)).ne')
  · intro diff
    obtain ⟨m,k,asym,hit⟩ := rational_schedule p q diff T pos
    exact ⟨m,k,(mode_injective p q diff).comp k.injective,asym,hit⟩

/-- Every two-prime false positive supplied for a nonempty rational schedule
has genuinely incommensurate energy gaps. -/
theorem incommensurate_witness (p q : Nat.Primes) (diff : p≠q) (T : Finset ℚ)
    (non : T.Nonempty) (pos : ∀ t ∈ T, 0<t) :
    ∃ (m : ℕ) (k : Fin m ↪ ℕ × ℕ), ¬Lattice.Sparse.Commensurate (mode p q ∘ k) ∧
      ¬Reflects (mode p q ∘ k) ∧ ∀ t ∈ T, agrees (mode p q ∘ k) (t : ℝ) := by
  obtain ⟨m,k,asym,pass⟩ := rational_schedule p q diff T pos
  refine ⟨m,k,fun grid => ?_,asym,pass⟩
  let a (i : Fin m) : ℕ+ := ⟨p.val^(k i).1*q.val^(k i).2,
    mul_pos (pow_pos p.property.pos _) (pow_pos q.property.pos _)⟩
  obtain ⟨t,ht⟩ := non
  have inj : Function.Injective (energy ∘ a) := (mode_injective p q diff).comp k.injective
  have alg : IsAlgebraic ℚ (t : ℝ) := isAlgebraic_algebraMap t
  have h := (Lattice.Sparse.commensurate_reading a inj grid _ alg).mp (pass t ht)
  exact asym (h.resolve_left (Rat.cast_pos.mpr (pos t ht)).ne')

/-- Every finite schedule of commensurable positive orders can be misleading
on a single nonisometric law, even with distinct energies on two prescribed modes. -/
theorem misleading_law (p q : Nat.Primes) (diff : p ≠ q) (T : Finset ℚ) (pos : ∀ t ∈ T, 0<t)
    (a : ℝ) (ha : 0<a) :
    let s : ℂ := (((1+a⁻¹)/2 : ℝ) : ℂ)
    ∃ (m : ℕ) (k : Fin m ↪ ℕ × ℕ), Function.Injective (mode p q ∘ k) ∧ ¬Reflects (mode p q ∘ k) ∧
      (∀ t ∈ T, lawOrder (finiteGibbsStateWeight (2*s.re-1) (mode p q ∘ k)) (a*(t : ℝ))) ∧
      ¬(∃ V : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, V f x=split s f x) := by
  dsimp only [Complex.ofReal_re]
  obtain ⟨m,k,asym,test⟩ := rational_schedule p q diff T pos
  refine ⟨m,k,(mode_injective p q diff).comp k.injective,asym,fun t ht => ?_,?_⟩
  · rw [gibbs_order,show 2*((1+a⁻¹)/2)-1=a⁻¹ by ring,show a*(t : ℝ)*a⁻¹=(t : ℝ) by field_simp]
    exact test t ht
  · rw [split_isometric_iff,Complex.ofReal_re]
    intro h
    linarith only [h,inv_pos.mpr ha]

#print axioms rational_schedule
#print axioms simple_schedule_iff
#print axioms incommensurate_witness
#print axioms misleading_law

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime
