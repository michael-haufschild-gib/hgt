import GaloisForLFunctions.RHTower.DeningerSuspendedAlternating
import GaloisForLFunctions.RHTower.DeningerExteriorPairSum

/-!
# The canonical primitive on the suspended source

A suspended head letter and its expansion carry the same product height and the same total
arithmetic character, and differ in letter count by one.  So the differential, which replaces the
head pair by its two constituents, costs exactly one factor `R`, and the averaged two-coproduct
primitive, which contracts the first two letters of a word into a head pair, saves one.

On the alternating part — the entire exterior completion — all `binom(r,2)` signed terms of the
averaged primitive agree, so the primitive is a strict section of the differential:

`d h = id`.

* `deningerSuspHeadPair`, `deningerSuspHeadExpand` : the head-pair word and its expansion.
* `deningerSuspHeadDiffCoe` : the differential on the head-pair sector.
* `deningerSuspPairPrimCoe` : the averaged two-coproduct primitive.
* `DeningerSuspAlternating`, `deningerSuspAltCoe_alternating` : the alternating part.
* `deningerSuspHeadDiff_pairPrim` : **`d h = id` on the alternating part.**
* `deningerSuspHeadDiff_seminormR_le`, `deningerSuspPairPrim_seminormR_le` : the two operators
  cost and save exactly one factor `R`.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## Head pairs and their expansions -/

/-- A word with a distinguished head pair: a pair of old letters followed by old letters. -/
abbrev DeningerSuspPair : Type :=
  Σ s : ℕ, (DeningerLattice × DeningerLattice) × (Fin s → DeningerLattice)

/-- The tuple of old letters underlying a head pair. -/
def deningerSuspPairVec (p : DeningerSuspPair) : Fin (p.1 + 2) → DeningerLattice :=
  Fin.cons (α := fun _ => DeningerLattice) p.2.1.1
    (Fin.cons (α := fun _ => DeningerLattice) p.2.1.2 p.2.2)

/-- The suspended word whose head letter is the suspended pair. -/
def deningerSuspHeadPair (p : DeningerSuspPair) : DeningerSuspWord :=
  ⟨p.1 + 1, Fin.cons (α := fun _ => DeningerSusp) (Sum.inr p.2.1) fun t => Sum.inl (p.2.2 t)⟩

/-- The word obtained by expanding the suspended head letter into its two constituents. -/
def deningerSuspHeadExpand (p : DeningerSuspPair) : DeningerSuspWord :=
  ⟨p.1 + 2, fun i => Sum.inl (deningerSuspPairVec p i)⟩

theorem deningerSuspHeadPair_height (p : DeningerSuspPair) :
    deningerSuspWordHeight (deningerSuspHeadPair p)
      = deningerHeight p.2.1.1 * (deningerHeight p.2.1.2 * ∏ t, deningerHeight (p.2.2 t)) := by
  obtain ⟨s, ⟨m, n⟩, g⟩ := p
  show (∏ i : Fin (s + 1),
      deningerSuspHeight (Fin.cons (α := fun _ => DeningerSusp) (Sum.inr (m, n))
        (fun t => Sum.inl (g t)) i)) = _
  rw [Fin.prod_univ_succ, Fin.cons_zero, deningerSuspHeight_inr]
  have hstep : ∀ t : Fin s,
      deningerSuspHeight (Fin.cons (α := fun _ => DeningerSusp) (Sum.inr (m, n))
          (fun t => Sum.inl (g t)) t.succ) = deningerHeight (g t) := by
    intro t
    rw [Fin.cons_succ]
    rfl
  rw [Finset.prod_congr rfl fun t _ => hstep t]
  ring

theorem deningerSuspHeadExpand_height (p : DeningerSuspPair) :
    deningerSuspWordHeight (deningerSuspHeadExpand p)
      = deningerHeight p.2.1.1 * (deningerHeight p.2.1.2 * ∏ t, deningerHeight (p.2.2 t)) := by
  obtain ⟨s, ⟨m, n⟩, g⟩ := p
  show (∏ i : Fin (s + 2),
      deningerSuspHeight (Sum.inl (Fin.cons (α := fun _ => DeningerLattice) m
        (Fin.cons (α := fun _ => DeningerLattice) n g) i))) = _
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  have h1 : ∀ i : Fin (s + 1),
      deningerSuspHeight (Sum.inl (Fin.cons (α := fun _ => DeningerLattice) m
          (Fin.cons (α := fun _ => DeningerLattice) n g) i.succ))
        = deningerSuspHeight (Sum.inl (Fin.cons (α := fun _ => DeningerLattice) n g i)) := by
    intro i
    rw [Fin.cons_succ]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Fin.prod_univ_succ, Fin.cons_zero]
  have h2 : ∀ t : Fin s,
      deningerSuspHeight (Sum.inl (Fin.cons (α := fun _ => DeningerLattice) n g t.succ))
        = deningerHeight (g t) := by
    intro t
    rw [Fin.cons_succ]
    rfl
  rw [Finset.prod_congr rfl fun t _ => h2 t, deningerSuspHeight_inl, deningerSuspHeight_inl]

/-- Expanding a head pair preserves the product of the letter heights. -/
theorem deningerSuspHeadExpand_height_eq (p : DeningerSuspPair) :
    deningerSuspWordHeight (deningerSuspHeadExpand p)
      = deningerSuspWordHeight (deningerSuspHeadPair p) := by
  rw [deningerSuspHeadExpand_height, deningerSuspHeadPair_height]

theorem deningerSuspHeadPair_char (p : DeningerSuspPair) :
    deningerSuspWordChar (deningerSuspHeadPair p)
      = p.2.1.1 + p.2.1.2 + ∑ t, p.2.2 t := by
  obtain ⟨s, ⟨m, n⟩, g⟩ := p
  show (∑ i : Fin (s + 1),
      deningerSuspChar (Fin.cons (α := fun _ => DeningerSusp) (Sum.inr (m, n))
        (fun t => Sum.inl (g t)) i)) = _
  rw [Fin.sum_univ_succ, Fin.cons_zero, deningerSuspChar_inr]
  have hstep : ∀ t : Fin s,
      deningerSuspChar (Fin.cons (α := fun _ => DeningerSusp) (Sum.inr (m, n))
          (fun t => Sum.inl (g t)) t.succ) = g t := by
    intro t
    rw [Fin.cons_succ]
    rfl
  rw [Finset.sum_congr rfl fun t _ => hstep t]

theorem deningerSuspHeadExpand_char (p : DeningerSuspPair) :
    deningerSuspWordChar (deningerSuspHeadExpand p)
      = p.2.1.1 + (p.2.1.2 + ∑ t, p.2.2 t) := by
  obtain ⟨s, ⟨m, n⟩, g⟩ := p
  show (∑ i : Fin (s + 2), deningerSuspChar (Sum.inl (Fin.cons (α := fun _ => DeningerLattice) m
      (Fin.cons (α := fun _ => DeningerLattice) n g) i))) = _
  rw [Fin.sum_univ_succ, Fin.cons_zero]
  have h1 : ∀ i : Fin (s + 1),
      deningerSuspChar (Sum.inl (Fin.cons (α := fun _ => DeningerLattice) m
          (Fin.cons (α := fun _ => DeningerLattice) n g) i.succ))
        = deningerSuspChar (Sum.inl (Fin.cons (α := fun _ => DeningerLattice) n g i)) := by
    intro i
    rw [Fin.cons_succ]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_succ, Fin.cons_zero]
  have h2 : ∀ t : Fin s,
      deningerSuspChar (Sum.inl (Fin.cons (α := fun _ => DeningerLattice) n g t.succ))
        = g t := by
    intro t
    rw [Fin.cons_succ]
    rfl
  rw [Finset.sum_congr rfl fun t _ => h2 t, deningerSuspChar_inl, deningerSuspChar_inl]

/-- **Expanding a head pair preserves the total arithmetic character.** -/
theorem deningerSuspHeadExpand_char_eq (p : DeningerSuspPair) :
    deningerSuspWordChar (deningerSuspHeadExpand p)
      = deningerSuspWordChar (deningerSuspHeadPair p) := by
  rw [deningerSuspHeadExpand_char, deningerSuspHeadPair_char, add_assoc]

/-- Expanding a head pair costs exactly one factor `R`. -/
theorem deningerSuspWeightR_headExpand (k : ℕ) (R : ℝ) (p : DeningerSuspPair) :
    deningerSuspWeightR k R (deningerSuspHeadExpand p)
      = R * deningerSuspWeightR k R (deningerSuspHeadPair p) := by
  rw [deningerSuspWeightR, deningerSuspWeightR, deningerSuspHeadExpand_height_eq]
  show R ^ (p.1 + 2) * _ = R * (R ^ (p.1 + 1) * _)
  ring

/-! ## Injectivity -/

theorem deningerSuspHeadPair_injective : Function.Injective deningerSuspHeadPair := by
  rintro ⟨s, ⟨m, n⟩, g⟩ ⟨s', ⟨m', n'⟩, g'⟩ h
  have hs : s + 1 = s' + 1 := congrArg Sigma.fst h
  have hs' : s = s' := by omega
  subst hs'
  have hfun : (Fin.cons (α := fun _ => DeningerSusp) (Sum.inr (m, n)) fun t => Sum.inl (g t))
      = (Fin.cons (α := fun _ => DeningerSusp) (Sum.inr (m', n')) fun t => Sum.inl (g' t)) :=
    eq_of_heq (Sigma.mk.inj h).2
  have h0 := congrFun hfun 0
  rw [Fin.cons_zero, Fin.cons_zero] at h0
  have hmn : (m, n) = (m', n') := Sum.inr_injective h0
  have hg : ∀ t : Fin s, g t = g' t := by
    intro t
    have := congrFun hfun t.succ
    rw [Fin.cons_succ, Fin.cons_succ] at this
    exact Sum.inl_injective this
  rw [hmn, funext hg]

theorem deningerSuspHeadExpand_injective : Function.Injective deningerSuspHeadExpand := by
  rintro ⟨s, ⟨m, n⟩, g⟩ ⟨s', ⟨m', n'⟩, g'⟩ h
  have hs : s + 2 = s' + 2 := congrArg Sigma.fst h
  have hs' : s = s' := by omega
  subst hs'
  have hfun : (fun i => Sum.inl (Fin.cons (α := fun _ => DeningerLattice) m
        (Fin.cons (α := fun _ => DeningerLattice) n g) i))
      = (fun i => Sum.inl (Fin.cons (α := fun _ => DeningerLattice) m'
        (Fin.cons (α := fun _ => DeningerLattice) n' g') i)) :=
    eq_of_heq (Sigma.mk.inj h).2
  have hvec : ∀ i : Fin (s + 2),
      Fin.cons (α := fun _ => DeningerLattice) m
          (Fin.cons (α := fun _ => DeningerLattice) n g) i
        = Fin.cons (α := fun _ => DeningerLattice) m'
          (Fin.cons (α := fun _ => DeningerLattice) n' g') i := by
    intro i
    exact Sum.inl_injective (congrFun hfun i)
  have hm : m = m' := by
    have := hvec 0
    rwa [Fin.cons_zero, Fin.cons_zero] at this
  have hn : n = n' := by
    have := hvec (0 : Fin (s + 1)).succ
    rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_zero, Fin.cons_zero] at this
    exact this
  have hg : ∀ t : Fin s, g t = g' t := by
    intro t
    have := hvec t.succ.succ
    rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ] at this
    exact this
  rw [hm, hn, funext hg]

/-! ## The differential on the head-pair sector -/

/-- **The differential**: the coefficient at an expanded word is the coefficient at the
corresponding head-pair word.  This is the single Leibniz term the odd derivation produces on a
word with one suspended letter. -/
def deningerSuspHeadDiffCoe (a : DeningerSuspWord → ℂ) : DeningerSuspWord → ℂ :=
  Function.extend deningerSuspHeadExpand (fun p => a (deningerSuspHeadPair p)) 0

@[simp]
theorem deningerSuspHeadDiffCoe_apply (a : DeningerSuspWord → ℂ) (p : DeningerSuspPair) :
    deningerSuspHeadDiffCoe a (deningerSuspHeadExpand p) = a (deningerSuspHeadPair p) :=
  deningerSuspHeadExpand_injective.extend_apply _ _ p

theorem deningerSuspHeadDiffCoe_zero (a : DeningerSuspWord → ℂ) {v : DeningerSuspWord}
    (hv : v ∉ Set.range deningerSuspHeadExpand) : deningerSuspHeadDiffCoe a v = 0 := by
  rw [deningerSuspHeadDiffCoe, Function.extend_apply' _ _ _ (by rintro ⟨p, rfl⟩; exact hv ⟨p, rfl⟩)]
  rfl

/-! ## The averaged two-coproduct primitive -/

/-- **The averaged two-coproduct primitive**: the coefficient at a head-pair word is the signed
average, over all ordered pairs of positions, of the coefficient at the word whose letters at those
two positions are the head pair.  No pair is chosen, so the formula is canonical. -/
def deningerSuspPairPrimCoe (a : DeningerSuspWord → ℂ) : DeningerSuspWord → ℂ :=
  Function.extend deningerSuspHeadPair
    (fun p => (((deningerPairIndex (p.1 + 2)).card : ℂ))⁻¹ *
      ∑ q ∈ deningerPairIndex (p.1 + 2),
        ((Equiv.Perm.sign (deningerPairPerm q.1 q.2) : ℤ) : ℂ) *
          a ⟨p.1 + 2, fun i =>
            Sum.inl (deningerSuspPairVec p (deningerPairPerm q.1 q.2 i))⟩) 0

theorem deningerSuspPairPrimCoe_zero (a : DeningerSuspWord → ℂ) {v : DeningerSuspWord}
    (hv : v ∉ Set.range deningerSuspHeadPair) : deningerSuspPairPrimCoe a v = 0 := by
  rw [deningerSuspPairPrimCoe,
    Function.extend_apply' _ _ _ (by rintro ⟨p, rfl⟩; exact hv ⟨p, rfl⟩)]
  rfl

/-! ## The alternating part -/

/-- A coefficient function is alternating when permuting the letters of a word multiplies it by the
sign of the permutation.  The entire exterior completion is exactly this subspace. -/
def DeningerSuspAlternating (a : DeningerSuspWord → ℂ) : Prop :=
  ∀ (r : ℕ) (f : Fin r → DeningerSusp) (σ : Equiv.Perm (Fin r)),
    a (deningerSuspPermute σ f) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * a (⟨r, f⟩ : DeningerSuspWord)

/-- **The antisymmetrizer lands in the alternating part.** -/
theorem deningerSuspAltCoe_alternating (a : DeningerSuspWord → ℂ) :
    DeningerSuspAlternating (deningerSuspAltCoe a) := by
  intro r f σ
  have hleft : deningerSuspAltCoe a (deningerSuspPermute σ f)
      = ((Nat.factorial r : ℂ))⁻¹ *
        ∑ τ : Equiv.Perm (Fin r),
          ((Equiv.Perm.sign τ : ℤ) : ℂ) * a (deningerSuspPermute (σ * τ) f) := by
    rw [deningerSuspAltCoe]
    rfl
  have hreindex : (∑ τ : Equiv.Perm (Fin r),
        ((Equiv.Perm.sign τ : ℤ) : ℂ) * a (deningerSuspPermute (σ * τ) f))
      = ∑ ρ : Equiv.Perm (Fin r),
          ((Equiv.Perm.sign (σ⁻¹ * ρ) : ℤ) : ℂ) * a (deningerSuspPermute ρ f) := by
    refine Fintype.sum_bijective (fun τ => σ * τ) (Group.mulLeft_bijective σ) _ _ fun τ => ?_
    rw [inv_mul_cancel_left]
  have hsign : ∀ ρ : Equiv.Perm (Fin r),
      ((Equiv.Perm.sign (σ⁻¹ * ρ) : ℤ) : ℂ)
        = ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign ρ : ℤ) : ℂ) := by
    intro ρ
    rw [map_mul, Equiv.Perm.sign_inv, Units.val_mul, Int.cast_mul]
  rw [hleft, hreindex, Finset.sum_congr rfl fun ρ _ => by rw [hsign ρ, mul_assoc],
    ← Finset.mul_sum, deningerSuspAltCoe]
  ring

/-- **The averaged primitive is a strict section on the alternating part.**  All `binom(r,2)`
signed terms agree there, so the average is the coefficient at the expanded word. -/
theorem deningerSuspPairPrimCoe_of_alternating {a : DeningerSuspWord → ℂ}
    (ha : DeningerSuspAlternating a) (p : DeningerSuspPair) :
    deningerSuspPairPrimCoe a (deningerSuspHeadPair p) = a (deningerSuspHeadExpand p) := by
  rw [deningerSuspPairPrimCoe, deningerSuspHeadPair_injective.extend_apply]
  have hterm : ∀ q ∈ deningerPairIndex (p.1 + 2),
      ((Equiv.Perm.sign (deningerPairPerm q.1 q.2) : ℤ) : ℂ) *
          a ⟨p.1 + 2, fun i =>
            Sum.inl (deningerSuspPairVec p (deningerPairPerm q.1 q.2 i))⟩
        = a (deningerSuspHeadExpand p) := by
    intro q _
    have hperm : (⟨p.1 + 2, fun i =>
          Sum.inl (deningerSuspPairVec p (deningerPairPerm q.1 q.2 i))⟩ : DeningerSuspWord)
        = deningerSuspPermute (deningerPairPerm q.1 q.2)
            (fun i => Sum.inl (deningerSuspPairVec p i)) := rfl
    rw [hperm, ha, ← mul_assoc]
    have hsq : ((Equiv.Perm.sign (deningerPairPerm q.1 q.2) : ℤ) : ℂ) *
        ((Equiv.Perm.sign (deningerPairPerm q.1 q.2) : ℤ) : ℂ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (deningerPairPerm q.1 q.2)) with hu | hu <;>
        rw [hu] <;> norm_num
    rw [hsq, one_mul]
    rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((deningerPairIndex (p.1 + 2)).card : ℂ) ≠ 0 := by
    have hpos : 0 < (deningerPairIndex (p.1 + 2)).card := by
      rw [deningerPairIndex_card]
      exact Nat.choose_pos (by omega)
    exact Nat.cast_ne_zero.mpr hpos.ne'
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- **`d h = id`.**  The differential of the averaged two-coproduct primitive is the identity on
the alternating part: the full completed Milnor ideal has a canonical strict primitive. -/
theorem deningerSuspHeadDiff_pairPrim {a : DeningerSuspWord → ℂ}
    (ha : DeningerSuspAlternating a) (p : DeningerSuspPair) :
    deningerSuspHeadDiffCoe (deningerSuspPairPrimCoe a) (deningerSuspHeadExpand p)
      = a (deningerSuspHeadExpand p) := by
  rw [deningerSuspHeadDiffCoe_apply, deningerSuspPairPrimCoe_of_alternating ha]

/-! ## The two seminorm estimates -/

/-- **The differential costs exactly one factor `R`.** -/
theorem deningerSuspHeadDiff_seminormR_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (c : DeningerSuspKothe) :
    (Summable fun v => deningerSuspWeightR k R v *
        ‖deningerSuspHeadDiffCoe (c : DeningerSuspWord → ℂ) v‖) ∧
      (∑' v, deningerSuspWeightR k R v *
          ‖deningerSuspHeadDiffCoe (c : DeningerSuspWord → ℂ) v‖)
        ≤ R * deningerSuspSeminormR k R c := by
  have hRpos : (0 : ℝ) < R := by linarith
  set G : DeningerSuspWord → ℝ := fun v =>
    deningerSuspWeightR k R v * ‖deningerSuspHeadDiffCoe (c : DeningerSuspWord → ℂ) v‖ with hGdef
  have hzero : ∀ v ∉ Set.range deningerSuspHeadExpand, G v = 0 := by
    intro v hv
    rw [hGdef]
    simp only
    rw [deningerSuspHeadDiffCoe_zero _ hv, norm_zero, mul_zero]
  have hcomp : ∀ p : DeningerSuspPair,
      G (deningerSuspHeadExpand p)
        = R * (deningerSuspWeightR k R (deningerSuspHeadPair p) *
            ‖(c : DeningerSuspWord → ℂ) (deningerSuspHeadPair p)‖) := by
    intro p
    rw [hGdef]
    simp only
    rw [deningerSuspHeadDiffCoe_apply, deningerSuspWeightR_headExpand]
    ring
  have hpair : Summable fun p : DeningerSuspPair =>
      deningerSuspWeightR k R (deningerSuspHeadPair p) *
        ‖(c : DeningerSuspWord → ℂ) (deningerSuspHeadPair p)‖ :=
    (deningerSuspSeminormR_summable hR c).comp_injective deningerSuspHeadPair_injective
  have hGcomp : Summable (G ∘ deningerSuspHeadExpand) := by
    refine (hpair.mul_left R).congr fun p => ?_
    exact (hcomp p).symm
  have hGsummable : Summable G :=
    (deningerSuspHeadExpand_injective.summable_iff hzero).mp hGcomp
  refine ⟨hGsummable, ?_⟩
  have hsupport : Function.support G ⊆ Set.range deningerSuspHeadExpand := by
    intro v hv
    by_contra hcon
    exact hv (hzero v hcon)
  have htsum : (∑' p : DeningerSuspPair, G (deningerSuspHeadExpand p)) = ∑' v, G v :=
    deningerSuspHeadExpand_injective.tsum_eq hsupport
  have hval : (∑' p : DeningerSuspPair, G (deningerSuspHeadExpand p))
      = R * ∑' p : DeningerSuspPair,
          deningerSuspWeightR k R (deningerSuspHeadPair p) *
            ‖(c : DeningerSuspWord → ℂ) (deningerSuspHeadPair p)‖ := by
    rw [← Summable.tsum_mul_left _ hpair]
    exact tsum_congr hcomp
  have hle : (∑' p : DeningerSuspPair,
        deningerSuspWeightR k R (deningerSuspHeadPair p) *
          ‖(c : DeningerSuspWord → ℂ) (deningerSuspHeadPair p)‖)
      ≤ deningerSuspSeminormR k R c := by
    refine Summable.tsum_le_tsum_of_inj deningerSuspHeadPair
      deningerSuspHeadPair_injective ?_ (fun p => le_of_eq rfl) hpair
      (deningerSuspSeminormR_summable hR c)
    intro v _
    exact mul_nonneg (deningerSuspWeightR_nonneg k hRpos.le v) (norm_nonneg _)
  rw [← htsum, hval]
  exact mul_le_mul_of_nonneg_left hle hRpos.le

/-- **The primitive saves exactly one factor `R`** on the alternating part: every defining
seminorm of the averaged primitive is at most the corresponding input seminorm. -/
theorem deningerSuspPairPrim_seminormR_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (c : DeningerSuspKothe) (ha : DeningerSuspAlternating (c : DeningerSuspWord → ℂ)) :
    (Summable fun v => deningerSuspWeightR k R v *
        ‖deningerSuspPairPrimCoe (c : DeningerSuspWord → ℂ) v‖) ∧
      (∑' v, deningerSuspWeightR k R v *
          ‖deningerSuspPairPrimCoe (c : DeningerSuspWord → ℂ) v‖)
        ≤ R⁻¹ * deningerSuspSeminormR k R c := by
  have hRpos : (0 : ℝ) < R := by linarith
  set G : DeningerSuspWord → ℝ := fun v =>
    deningerSuspWeightR k R v * ‖deningerSuspPairPrimCoe (c : DeningerSuspWord → ℂ) v‖ with hGdef
  have hzero : ∀ v ∉ Set.range deningerSuspHeadPair, G v = 0 := by
    intro v hv
    rw [hGdef]
    simp only
    rw [deningerSuspPairPrimCoe_zero _ hv, norm_zero, mul_zero]
  have hcomp : ∀ p : DeningerSuspPair,
      G (deningerSuspHeadPair p)
        = R⁻¹ * (deningerSuspWeightR k R (deningerSuspHeadExpand p) *
            ‖(c : DeningerSuspWord → ℂ) (deningerSuspHeadExpand p)‖) := by
    intro p
    rw [hGdef]
    simp only
    rw [deningerSuspPairPrimCoe_of_alternating ha, deningerSuspWeightR_headExpand]
    field_simp
  have hexp : Summable fun p : DeningerSuspPair =>
      deningerSuspWeightR k R (deningerSuspHeadExpand p) *
        ‖(c : DeningerSuspWord → ℂ) (deningerSuspHeadExpand p)‖ :=
    (deningerSuspSeminormR_summable hR c).comp_injective deningerSuspHeadExpand_injective
  have hGcomp : Summable (G ∘ deningerSuspHeadPair) := by
    refine (hexp.mul_left R⁻¹).congr fun p => ?_
    exact (hcomp p).symm
  have hGsummable : Summable G :=
    (deningerSuspHeadPair_injective.summable_iff hzero).mp hGcomp
  refine ⟨hGsummable, ?_⟩
  have hsupport : Function.support G ⊆ Set.range deningerSuspHeadPair := by
    intro v hv
    by_contra hcon
    exact hv (hzero v hcon)
  have htsum : (∑' p : DeningerSuspPair, G (deningerSuspHeadPair p)) = ∑' v, G v :=
    deningerSuspHeadPair_injective.tsum_eq hsupport
  have hval : (∑' p : DeningerSuspPair, G (deningerSuspHeadPair p))
      = R⁻¹ * ∑' p : DeningerSuspPair,
          deningerSuspWeightR k R (deningerSuspHeadExpand p) *
            ‖(c : DeningerSuspWord → ℂ) (deningerSuspHeadExpand p)‖ := by
    rw [← Summable.tsum_mul_left _ hexp]
    exact tsum_congr hcomp
  have hle : (∑' p : DeningerSuspPair,
        deningerSuspWeightR k R (deningerSuspHeadExpand p) *
          ‖(c : DeningerSuspWord → ℂ) (deningerSuspHeadExpand p)‖)
      ≤ deningerSuspSeminormR k R c := by
    refine Summable.tsum_le_tsum_of_inj deningerSuspHeadExpand
      deningerSuspHeadExpand_injective ?_ (fun p => le_of_eq rfl) hexp
      (deningerSuspSeminormR_summable hR c)
    intro v _
    exact mul_nonneg (deningerSuspWeightR_nonneg k hRpos.le v) (norm_nonneg _)
  rw [← htsum, hval]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end RHTower
