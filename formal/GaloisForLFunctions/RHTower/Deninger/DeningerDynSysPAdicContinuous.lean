import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysValuedTriples

/-!
# `p`-adically continuous pointed multiplicative maps

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Definition 14.2
(`t91`) and Proposition 14.4 (`t124`).

Deninger singles out the subspace `X̂_c (𝒪) ⊆ X̂ (𝒪)` of those triples whose multiplicative map
factors over the `p`-adic completion, i.e. is `p`-adically continuous.  Written out, this is the
elementary condition

`∀ n, ∃ m, a - b ∈ (p ^ m) → P a - P b ∈ (p ^ n)` ,

which needs no topology.  Two facts make `X̂_c (𝒪)` a subsystem: additive maps — in particular the
ring homomorphisms coming from honest `𝒪`-valued points of `X`, which is Proposition 14.4 — are
`p`-adically continuous, and the condition is preserved by the Frobenius operator `P ↦ P ^ p`,
because `u ^ p - v ^ p` is a multiple of `u - v`.
-/

namespace RHTower

variable {A O : Type*} [CommRing A] [CommRing O]

/-- **Deninger, Definition 14.2 (`t91`).**  A map is `p`-adically continuous when congruences
modulo high powers of `p` are preserved. -/
def DeningerPAdicContinuous (p : ℕ) (P : A → O) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, ∀ a b : A, a - b ∈ (Ideal.span {(p : A)}) ^ m →
    P a - P b ∈ (Ideal.span {(p : O)}) ^ n

/-- **Deninger, Proposition 14.4 (`t124`).**  A ring homomorphism is `p`-adically continuous; in
particular the multiplicative maps coming from honest `𝒪`-valued points lie in `X̂_c (𝒪)`. -/
theorem deningerPAdicContinuous_of_ringHom (p : ℕ) (f : A →+* O) :
    DeningerPAdicContinuous p (f : A → O) := by
  intro n
  refine ⟨n, fun a b hab => ?_⟩
  have hmap : f a - f b = f (a - b) := (map_sub f a b).symm
  rw [hmap]
  have hspan : (Ideal.span {(p : A)}) ^ n = Ideal.span {((p : A)) ^ n} := by
    rw [Ideal.span_singleton_pow]
  rw [hspan, Ideal.mem_span_singleton] at hab
  obtain ⟨c, hc⟩ := hab
  rw [hc, map_mul, map_pow, map_natCast]
  have : (Ideal.span {(p : O)}) ^ n = Ideal.span {((p : O)) ^ n} := by
    rw [Ideal.span_singleton_pow]
  rw [this, Ideal.mem_span_singleton]
  exact Dvd.intro _ rfl

/-- `u ^ p - v ^ p` is a multiple of `u - v`. -/
theorem deningerSub_dvd_pow_sub_pow (u v : O) (k : ℕ) : (u - v) ∣ u ^ k - v ^ k :=
  sub_dvd_pow_sub_pow u v k

/-- **Deninger, Definition 14.2 (`t91`).**  The Frobenius operator preserves `p`-adic
continuity. -/
theorem deningerPAdicContinuous_pow {p : ℕ} {P : A → O} (hP : DeningerPAdicContinuous p P)
    (k : ℕ) : DeningerPAdicContinuous p (fun a => P a ^ k) := by
  intro n
  obtain ⟨m, hm⟩ := hP n
  refine ⟨m, fun a b hab => ?_⟩
  obtain ⟨c, hc⟩ := deningerSub_dvd_pow_sub_pow (P a) (P b) k
  rw [hc]
  exact Ideal.mul_mem_right _ _ (hm a b hab)

/-- **Deninger, Definition 14.2 (`t91`).**  The subspace `X̂_c (𝒪)` of `p`-adically continuous
`𝒪`-valued triples. -/
def DeningerValuedTripleC (X : AlgebraicGeometry.Scheme) (O : Type) [CommRing O] [IsLocalRing O]
    (p : ℕ) : Set (DeningerValuedTriple X O) :=
  {P | DeningerPAdicContinuous p (P.map : DeningerClosureLocalRing P.specializes → O)}

/-- The Frobenius operator on `𝒪`-valued triples. -/
noncomputable def deningerValuedTripleFrobenius {X : AlgebraicGeometry.Scheme} {O : Type}
    [CommRing O] [IsLocalRing O] [IsDomain O] (k : ℕ) (hk : 0 < k)
    (P : DeningerValuedTriple X O) : DeningerValuedTriple X O where
  gen := P.gen
  spec := P.spec
  specializes := P.specializes
  map :=
    { toFun := fun f => P.map f ^ k
      map_zero' := by simp [hk.ne']
      map_one' := by simp
      map_mul' := fun a b => by simp [mul_pow] }
  map_ne_zero := fun f hf hz => by
    have h0 : P.map f = 0 := by
      have := pow_eq_zero_iff (n := k) hk.ne' |>.1 hz
      exact this
    exact P.map_ne_zero f hf h0
  map_residue := fun f g hfg => by
    obtain ⟨c, hc⟩ := deningerSub_dvd_pow_sub_pow (P.map f) (P.map g) k
    show P.map f ^ k - P.map g ^ k ∈ IsLocalRing.maximalIdeal O
    rw [hc]
    exact Ideal.mul_mem_right _ _ (P.map_residue f g hfg)

/-- **Deninger, Definition 14.2 (`t91`).**  `X̂_c (𝒪)` is invariant under the Frobenius
operator. -/
theorem deningerValuedTripleC_frobenius {X : AlgebraicGeometry.Scheme} {O : Type}
    [CommRing O] [IsLocalRing O] [IsDomain O] {p k : ℕ} (hk : 0 < k)
    {P : DeningerValuedTriple X O} (hP : P ∈ DeningerValuedTripleC X O p) :
    deningerValuedTripleFrobenius k hk P ∈ DeningerValuedTripleC X O p :=
  deningerPAdicContinuous_pow hP k

end RHTower
