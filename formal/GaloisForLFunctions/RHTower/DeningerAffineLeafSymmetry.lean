import GaloisForLFunctions.RHTower.DeningerAffineLeafFlow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Symmetries of the affine leaf distribution

The affine distribution is preserved by the deck maps of the suspension, by Galois maps, and it is
genuinely of rank two.

The deck map raises the character to a power, scales the Kummer vector by the same factor, and
divides the suspension height by it.  It commutes with both flows because raising the phase
character to a power is the same as scaling its Kummer vector.  A Galois map permutes the character
lattice and acts on the Kummer space by an isometry matching the Kummer family; it commutes with
both flows because an isometry preserves the pairing that defines the phase.

Rank two is the injectivity of the map sending `(s, t)` to the pair of infinitesimal generators:
the modulus generator lives in the Kummer coordinate and is nonzero because the Kummer vector is,
and the phase generator lives in the character coordinate and is nonzero because the Kummer
functional of a nonzero vector does not vanish identically.

* `deningerFrobenius_modulus`, `deningerFrobenius_phase`, `deningerFrobenius_affine` : deck
  equivariance.
* `deningerGalois_modulus`, `deningerGalois_phase`, `deningerGalois_affine` : Galois equivariance.
* `deningerAffineTangent_injective`, `deningerAffineGenerators_linearIndependent` : rank two.
* `deningerModulusFlow_hasDerivAt`, `deningerPhaseFlow_hasDerivAt`, `deningerBracket_hasDerivAt` :
  the two generators and the infinitesimal bracket relation.
-/

namespace RHTower

open scoped InnerProductSpace

section Symmetry

variable {V : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The deck map of the suspension** at a positive integer level: it raises the character to the
power, scales the Kummer vector, and divides the suspension height. -/
noncomputable def deningerFrobenius (n : ℕ) (hn : 0 < n) (p : DeningerFinePoint V H) :
    DeningerFinePoint V H where
  chi := p.chi ^ n
  vec := (n : ℝ) • p.vec
  vec_ne_zero := smul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') p.vec_ne_zero
  susp := p.susp / n
  susp_pos := div_pos p.susp_pos (Nat.cast_pos.mpr hn)

@[simp] theorem deningerFrobenius_chi (n : ℕ) (hn : 0 < n) (p : DeningerFinePoint V H) :
    (deningerFrobenius n hn p).chi = p.chi ^ n := rfl

@[simp] theorem deningerFrobenius_vec (n : ℕ) (hn : 0 < n) (p : DeningerFinePoint V H) :
    (deningerFrobenius n hn p).vec = (n : ℝ) • p.vec := rfl

/-- **The deck map commutes with the modulus flow.** -/
theorem deningerFrobenius_modulus (n : ℕ) (hn : 0 < n) (s : ℝ) (p : DeningerFinePoint V H) :
    deningerFrobenius n hn (deningerModulusFlow s p)
      = deningerModulusFlow s (deningerFrobenius n hn p) := by
  refine DeningerFinePoint.ext' rfl ?_ rfl
  show (n : ℝ) • (Real.exp s • p.vec) = Real.exp s • ((n : ℝ) • p.vec)
  rw [smul_comm]

/-- **The deck map commutes with the phase flow.**  Raising the phase character to the power `n` is
the same as scaling its Kummer vector by `n`. -/
theorem deningerFrobenius_phase (f : V → H) (n : ℕ) (hn : 0 < n) (t : ℝ)
    (p : DeningerFinePoint V H) :
    deningerFrobenius n hn (deningerPhaseFlow f t p)
      = deningerPhaseFlow f t (deningerFrobenius n hn p) := by
  refine DeningerFinePoint.ext' ?_ rfl rfl
  show (p.chi * deningerKappa f p.vec t) ^ n
      = p.chi ^ n * deningerKappa f ((n : ℝ) • p.vec) t
  rw [mul_pow, deningerKappa_pow]

/-- **The deck map commutes with the affine flow**, hence carries leaves to leaves. -/
theorem deningerFrobenius_affine (f : V → H) (n : ℕ) (hn : 0 < n) (s t : ℝ)
    (p : DeningerFinePoint V H) :
    deningerFrobenius n hn (deningerAffineFlow f s t p)
      = deningerAffineFlow f s t (deningerFrobenius n hn p) := by
  rw [deningerAffineFlow, deningerAffineFlow, deningerFrobenius_modulus, deningerFrobenius_phase]

/-- **The deck map carries the leaf through a point to the leaf through its image.** -/
theorem deningerFrobenius_mem_leaf (f : V → H) (n : ℕ) (hn : 0 < n)
    {p q : DeningerFinePoint V H} (hq : q ∈ deningerAffineLeaf f p) :
    deningerFrobenius n hn q ∈ deningerAffineLeaf f (deningerFrobenius n hn p) := by
  obtain ⟨⟨s, t⟩, rfl⟩ := hq
  exact ⟨(s, t), (deningerFrobenius_affine f n hn s t p).symm⟩

/-- **The Galois map** attached to a permutation of the character lattice and an isometry of the
Kummer space. -/
noncomputable def deningerGalois (σ : V ≃ V) (U : H ≃ₗᵢ[ℝ] H) (p : DeningerFinePoint V H) :
    DeningerFinePoint V H where
  chi := fun b => p.chi (σ.symm b)
  vec := U p.vec
  vec_ne_zero := by
    intro hz
    refine p.vec_ne_zero ?_
    have h := congrArg U.symm hz
    simpa using h
  susp := p.susp
  susp_pos := p.susp_pos

@[simp] theorem deningerGalois_vec (σ : V ≃ V) (U : H ≃ₗᵢ[ℝ] H) (p : DeningerFinePoint V H) :
    (deningerGalois σ U p).vec = U p.vec := rfl

/-- **An isometry matching the Kummer family preserves the Kummer functional.**  This is the
invariance of the pairing under Galois. -/
theorem deningerKummerForm_galois {f : V → H} {σ : V ≃ V} {U : H ≃ₗᵢ[ℝ] H}
    (hf : ∀ a : V, f (σ a) = U (f a)) (h : H) (a : V) :
    deningerKummerForm f (U h) (σ a) = deningerKummerForm f h a := by
  rw [deningerKummerForm, deningerKummerForm, hf a, U.inner_map_map]

/-- The phase character transforms by the permutation of the lattice. -/
theorem deningerKappa_galois {f : V → H} {σ : V ≃ V} {U : H ≃ₗᵢ[ℝ] H}
    (hf : ∀ a : V, f (σ a) = U (f a)) (h : H) (t : ℝ) (b : V) :
    deningerKappa f (U h) t b = deningerKappa f h t (σ.symm b) := by
  have hb := deningerKummerForm_galois hf h (σ.symm b)
  rw [Equiv.apply_symm_apply] at hb
  rw [deningerKappa, deningerKappa, hb]

/-- **The Galois map commutes with the modulus flow.** -/
theorem deningerGalois_modulus (σ : V ≃ V) (U : H ≃ₗᵢ[ℝ] H) (s : ℝ) (p : DeningerFinePoint V H) :
    deningerGalois σ U (deningerModulusFlow s p)
      = deningerModulusFlow s (deningerGalois σ U p) := by
  refine DeningerFinePoint.ext' rfl ?_ rfl
  show U (Real.exp s • p.vec) = Real.exp s • U p.vec
  rw [map_smul]

/-- **The Galois map commutes with the phase flow.** -/
theorem deningerGalois_phase {f : V → H} {σ : V ≃ V} {U : H ≃ₗᵢ[ℝ] H}
    (hf : ∀ a : V, f (σ a) = U (f a)) (t : ℝ) (p : DeningerFinePoint V H) :
    deningerGalois σ U (deningerPhaseFlow f t p)
      = deningerPhaseFlow f t (deningerGalois σ U p) := by
  refine DeningerFinePoint.ext' ?_ rfl rfl
  funext b
  show p.chi (σ.symm b) * deningerKappa f p.vec t (σ.symm b)
      = p.chi (σ.symm b) * deningerKappa f (U p.vec) t b
  rw [deningerKappa_galois hf]

/-- **The Galois map commutes with the affine flow**, hence carries leaves to leaves. -/
theorem deningerGalois_affine {f : V → H} {σ : V ≃ V} {U : H ≃ₗᵢ[ℝ] H}
    (hf : ∀ a : V, f (σ a) = U (f a)) (s t : ℝ) (p : DeningerFinePoint V H) :
    deningerGalois σ U (deningerAffineFlow f s t p)
      = deningerAffineFlow f s t (deningerGalois σ U p) := by
  rw [deningerAffineFlow, deningerAffineFlow, deningerGalois_modulus, deningerGalois_phase hf]

/-- **The Galois map carries the leaf through a point to the leaf through its image.** -/
theorem deningerGalois_mem_leaf {f : V → H} {σ : V ≃ V} {U : H ≃ₗᵢ[ℝ] H}
    (hf : ∀ a : V, f (σ a) = U (f a)) {p q : DeningerFinePoint V H}
    (hq : q ∈ deningerAffineLeaf f p) :
    deningerGalois σ U q ∈ deningerAffineLeaf f (deningerGalois σ U p) := by
  obtain ⟨⟨s, t⟩, rfl⟩ := hq
  exact ⟨(s, t), (deningerGalois_affine hf s t p).symm⟩

end Symmetry

section RankTwo

variable {V : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The pair of infinitesimal generators of the affine action at a Kummer vector: the modulus
generator in the Kummer coordinate and the phase generator in the character coordinate. -/
noncomputable def deningerAffineTangentMap (f : V → H) (h : H) :
    (ℝ × ℝ) →ₗ[ℝ] H × (V → ℝ) where
  toFun c := (c.1 • h, fun a => c.2 * deningerKummerForm f h a)
  map_add' c₁ c₂ := by
    refine Prod.ext ?_ ?_
    · show (c₁.1 + c₂.1) • h = c₁.1 • h + c₂.1 • h
      rw [add_smul]
    · funext a
      show (c₁.2 + c₂.2) * deningerKummerForm f h a
          = c₁.2 * deningerKummerForm f h a + c₂.2 * deningerKummerForm f h a
      ring
  map_smul' r c := by
    refine Prod.ext ?_ ?_
    · show (r * c.1) • h = r • (c.1 • h)
      rw [mul_smul]
    · funext a
      show (r * c.2) * deningerKummerForm f h a = r * (c.2 * deningerKummerForm f h a)
      ring

@[simp] theorem deningerAffineTangentMap_apply (f : V → H) (h : H) (c : ℝ × ℝ) :
    deningerAffineTangentMap f h c = (c.1 • h, fun a => c.2 * deningerKummerForm f h a) := rfl

/-- **The affine distribution has rank two.**  The modulus generator is nonzero because the Kummer
vector is, and the phase generator is nonzero because the Kummer functional of a nonzero vector
does not vanish identically; the two live in different coordinates. -/
theorem deningerAffineTangent_injective {f : V → H} {h : H} (hh : h ≠ 0)
    (hK : ∃ a : V, deningerKummerForm f h a ≠ 0) :
    Function.Injective (deningerAffineTangentMap f h) := by
  obtain ⟨a, ha⟩ := hK
  rw [injective_iff_map_eq_zero]
  intro c hc
  rw [deningerAffineTangentMap_apply, Prod.ext_iff] at hc
  obtain ⟨h1, h2⟩ := hc
  have hc1 : c.1 = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hh
  have hc2 : c.2 = 0 := by
    have := congrFun h2 a
    exact (mul_eq_zero.mp this).resolve_right ha
  exact Prod.ext hc1 hc2

/-- **The two generators are linearly independent.** -/
theorem deningerAffineGenerators_linearIndependent {f : V → H} {h : H} (hh : h ≠ 0)
    (hK : ∃ a : V, deningerKummerForm f h a ≠ 0) :
    LinearIndependent ℝ
      ![deningerAffineTangentMap f h (1, 0), deningerAffineTangentMap f h (0, 1)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hmap : s • deningerAffineTangentMap f h (1, 0) + t • deningerAffineTangentMap f h (0, 1)
      = deningerAffineTangentMap f h (s, t) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    refine Prod.ext ?_ ?_
    · show s * 1 + t * 0 = s
      ring
    · show s * 0 + t * 1 = t
      ring
  rw [hmap] at hst
  have hzero : deningerAffineTangentMap f h (s, t) = deningerAffineTangentMap f h 0 := by
    rw [hst, map_zero]
  have := deningerAffineTangent_injective hh hK hzero
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- **The modulus Euler field is the derivative of the modulus flow.** -/
theorem deningerModulusFlow_hasDerivAt (p : DeningerFinePoint V H) :
    HasDerivAt (fun s => (deningerModulusFlow s p).vec) p.vec 0 := by
  have h : HasDerivAt (fun s : ℝ => Real.exp s • p.vec) (Real.exp 0 • p.vec) 0 :=
    (Real.hasDerivAt_exp 0).smul_const p.vec
  rw [Real.exp_zero, one_smul] at h
  exact h

/-- **The Kummer–Kronecker phase field is the derivative of the phase flow**, read in the exponent
coordinate of the character. -/
theorem deningerPhaseFlow_hasDerivAt (f : V → H) (h : H) (a : V) :
    HasDerivAt (fun t : ℝ => t * deningerKummerForm f h a) (deningerKummerForm f h a) 0 := by
  simpa using (hasDerivAt_id (0 : ℝ)).mul_const (deningerKummerForm f h a)

/-- **The infinitesimal bracket relation.**  Differentiating the conjugation law
`deningerModulus_phase_conjugation` in the modulus time at zero rescales the phase time by `-1`,
which is the relation `[A, K] = K` up to the orientation of the bracket. -/
theorem deningerBracket_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s) * t) (-t) 0 := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) 0 := (hasDerivAt_id (0 : ℝ)).neg
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-(0 : ℝ)) * (-1)) 0 := hneg.exp
  have h := hexp.mul_const t
  have hval : Real.exp (-(0 : ℝ)) * (-1) * t = -t := by
    rw [neg_zero, Real.exp_zero]
    ring
  rw [hval] at h
  exact h

end RankTwo

end RHTower
