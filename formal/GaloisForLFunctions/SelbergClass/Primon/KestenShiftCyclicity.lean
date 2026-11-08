import GaloisForLFunctions.SelbergClass.Primon.KestenShiftOperators

/-!
# Prime likelihoods are cyclic vectors for spectral creation

The depth-`N` normalized likelihood tail is exactly the `N`-fold raising
orbit of the prime likelihood. Adjacent orbit vectors recover every even
character. Every prime is therefore cyclic for the same pure isometry.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- A normalized likelihood tail in the completed likelihood Hilbert space. -/
def kestenTailState (p : Nat.Primes) (N : ℕ) : KestenLikelihoodHilbert :=
  ⟨kestenNormalizedTail p N, kestenNormalizedTail_mem_likelihoodHilbert p N⟩

@[simp] theorem coe_kestenTailState (p : Nat.Primes) (N : ℕ) :
    (kestenTailState p N : SemicircleL2) = kestenNormalizedTail p N := rfl

/-- Tail coordinates are a geometric sequence preceded by exactly `N` zeros. -/
theorem hardyCoordinate_kestenTailState (p : Nat.Primes) (N m : ℕ) :
    hardyLikelihoodUnitary.symm (kestenTailState p N) m =
      if N ≤ m then primeReciprocal p ^ (m - N) else 0 := by
  rw [hardyLikelihoodUnitary_symm_coordinate, coe_kestenTailState]
  by_cases h : N ≤ m
  · rw [if_pos h]
    have he := inner_kestenNormalizedTail_later p N (m - N)
    rwa [Nat.add_sub_of_le h] at he
  · rw [if_neg h, inner_kestenNormalizedTail_earlier p N m (by omega)]

/-- The depth-zero state is the actual prime likelihood. -/
theorem kestenTailState_zero (p : Nat.Primes) : kestenTailState p 0 = kestenPrimeState p := by
  apply Subtype.ext
  rw [coe_kestenTailState, kestenNormalizedTail_zero, coe_kestenPrimeState]

/-- Spectral creation raises normalized likelihood-tail depth by one. -/
theorem kestenShift_tail (p : Nat.Primes) (N : ℕ) :
    kestenShift (kestenTailState p N) = kestenTailState p (N + 1) := by
  apply hardyLikelihoodUnitary.symm.injective
  apply lp.ext
  funext m
  rw [hardyCoordinate_kestenShift]
  cases m with
  | zero =>
      rw [shiftSeq_zero, hardyCoordinate_kestenTailState, if_neg (by omega)]
  | succ m =>
      rw [shiftSeq_succ, hardyCoordinate_kestenTailState, hardyCoordinate_kestenTailState]
      by_cases h : N ≤ m
      · rw [if_pos h, if_pos (by omega)]
        congr 1
        omega
      · rw [if_neg h, if_neg (by omega)]

/-- Every normalized prime tail is an actual iterate of the same raising operator. -/
theorem iterate_kestenShift_prime (p : Nat.Primes) (N : ℕ) :
    (kestenShift : KestenLikelihoodHilbert → KestenLikelihoodHilbert)^[N]
      (kestenPrimeState p) = kestenTailState p N := by
  induction N with
  | zero => exact (kestenTailState_zero p).symm
  | succ N ih => rw [Function.iterate_succ_apply', ih, kestenShift_tail]

/-- Lowering reverses a positive-depth normalized likelihood tail. -/
theorem kestenBackshift_tail_succ (p : Nat.Primes) (N : ℕ) :
    kestenBackshift (kestenTailState p (N + 1)) = kestenTailState p N := by
  rw [← kestenShift_tail, kestenBackshift_shift]

/-- A finite difference of adjacent orbit states is exactly one even character. -/
theorem kestenTailState_innovation (p : Nat.Primes) (N : ℕ) :
    kestenTailState p N - primeReciprocal p • kestenTailState p (N + 1) =
      kestenCharacterState N := by
  apply Subtype.ext
  change kestenNormalizedTail p N - primeReciprocal p • kestenNormalizedTail p (N + 1) =
    (kestenCharacterState N : SemicircleL2)
  rw [coe_kestenCharacterState, kestenNormalizedTail_innovation]

/-- Every actual prime likelihood is a cyclic vector for the spectral raising isometry. -/
theorem kestenShift_prime_cyclic (p : Nat.Primes) :
    (Submodule.span ℝ (Set.range (fun N : ℕ =>
      (kestenShift : KestenLikelihoodHilbert → KestenLikelihoodHilbert)^[N]
        (kestenPrimeState p)))).topologicalClosure = ⊤ := by
  let V := Submodule.span ℝ (Set.range (fun N : ℕ =>
    (kestenShift : KestenLikelihoodHilbert → KestenLikelihoodHilbert)^[N]
      (kestenPrimeState p)))
  have htail (N : ℕ) : kestenTailState p N ∈ V :=
    Submodule.subset_span ⟨N, iterate_kestenShift_prime p N⟩
  have hchar (N : ℕ) : kestenCharacterState N ∈ V := by
    rw [← kestenTailState_innovation p N]
    exact V.sub_mem (htail N) (V.smul_mem _ (htail (N + 1)))
  have horth : Vᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro f hf
    change f = 0
    apply hardyLikelihoodUnitary.symm.injective
    apply lp.ext
    funext n
    have hn := hf _ (hchar n)
    rw [inner_kestenCharacterState] at hn
    simpa only [map_zero, lp.coeFn_zero, Pi.zero_apply] using hn
  change V.topologicalClosure = ⊤
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]

private theorem coordinate_iterate_shift_zero (N m : ℕ) (h : m < N)
    (f : KestenLikelihoodHilbert) :
    hardyLikelihoodUnitary.symm
      ((kestenShift : KestenLikelihoodHilbert → KestenLikelihoodHilbert)^[N] f) m = 0 := by
  induction N generalizing m with
  | zero => omega
  | succ N ih =>
      rw [Function.iterate_succ_apply', hardyCoordinate_kestenShift]
      cases m with
      | zero => rfl
      | succ m => exact ih m (by omega)

/-- No nonzero state lies in every raising range: the likelihood shift is pure. -/
theorem kestenShift_pure (f : KestenLikelihoodHilbert) :
    (∀ N : ℕ, f ∈ Set.range
      ((kestenShift : KestenLikelihoodHilbert → KestenLikelihoodHilbert)^[N])) ↔ f = 0 := by
  constructor
  · intro h
    apply hardyLikelihoodUnitary.symm.injective
    apply lp.ext
    funext n
    obtain ⟨g, hg⟩ := h (n + 1)
    have hz := coordinate_iterate_shift_zero (n + 1) n (by omega) g
    rw [hg] at hz
    simpa only [map_zero, lp.coeFn_zero, Pi.zero_apply] using hz
  · rintro rfl N
    refine ⟨0, ?_⟩
    induction N with
    | zero => rfl
    | succ N ih => rw [Function.iterate_succ_apply', ih, map_zero]

end
end GaloisForLFunctions.SelbergClass.Primon

