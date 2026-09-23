import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Order.Group.Nat

/-!
# Characters extend uniquely along a `q`-radicial inclusion

If `ι : A → B` is an injective homomorphism of commutative groups such that every element of `B`
has a `q^n`-th power in the image, then restriction along `ι` is a bijection on homomorphisms into
any commutative group on which the `q`-th power map is bijective: a character of `A` extends to
`B` by taking `q^n`-th roots, and the extension is unique because `q`-th powers are injective.

This is the group-theoretic content of the passage from a field to a purely inseparable extension
in characteristic `q`.
-/

namespace HTGeometry

universe u v w

variable {A : Type u} {B : Type v} {C : Type w} [CommGroup A] [CommGroup B] [CommGroup C]

/-- Restriction along a `q`-radicial inclusion is injective on characters. -/
theorem charRestrict_injective (ι : A →* B) (q : ℕ)
    (hq : Function.Injective fun c : C => c ^ q)
    (hpow : ∀ b : B, ∃ (n : ℕ) (a : A), ι a = b ^ q ^ n)
    {f g : B →* C} (h : f.comp ι = g.comp ι) : f = g := by
  have hqiter : ∀ (n : ℕ), Function.Injective fun c : C => c ^ q ^ n := by
    intro n
    induction n with
    | zero => intro x y hxy; simpa using hxy
    | succ n ih =>
        intro x y hxy
        refine ih ?_
        refine hq ?_
        show (x ^ q ^ n) ^ q = (y ^ q ^ n) ^ q
        rw [← pow_mul, ← pow_mul, ← pow_succ]
        exact hxy
  refine MonoidHom.ext fun b => ?_
  obtain ⟨n, a, ha⟩ := hpow b
  refine hqiter n ?_
  show f b ^ q ^ n = g b ^ q ^ n
  rw [← map_pow, ← map_pow, ← ha]
  exact congrArg (fun F : A →* C => F a) h

variable (ι : A →* B) (hι : Function.Injective ι) (q : ℕ)
variable (hq : Function.Bijective fun c : C => c ^ q)

/-- The `q`-th power automorphism of a uniquely `q`-divisible commutative group. -/
noncomputable def powMulEquiv : C ≃* C := MulEquiv.ofBijective (powMonoidHom q) hq

theorem powMulEquiv_apply (c : C) : powMulEquiv q hq c = c ^ q := rfl

theorem powMulEquiv_iterate (k : ℕ) (c : C) :
    (powMulEquiv q hq : C → C)^[k] c = c ^ q ^ k := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih, powMulEquiv_apply, ← pow_mul, ← pow_succ']

theorem powMulEquiv_symm_iterate_mul (k : ℕ) (x y : C) :
    ((powMulEquiv q hq).symm : C → C)^[k] (x * y)
      = ((powMulEquiv q hq).symm : C → C)^[k] x * ((powMulEquiv q hq).symm : C → C)^[k] y := by
  induction k generalizing x y with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, map_mul, ih]

include hι in
/-- Two witnesses for the same element give the same root. -/
theorem charRoot_well_defined (g : A →* C) (b : B) (n m : ℕ) (a a' : A)
    (han : ι a = b ^ q ^ n) (ham : ι a' = b ^ q ^ m) :
    ((powMulEquiv q hq).symm : C → C)^[n] (g a)
      = ((powMulEquiv q hq).symm : C → C)^[m] (g a') := by
  have key : ∀ (n m : ℕ) (a a' : A), n ≤ m → ι a = b ^ q ^ n → ι a' = b ^ q ^ m →
      ((powMulEquiv q hq).symm : C → C)^[n] (g a)
        = ((powMulEquiv q hq).symm : C → C)^[m] (g a') := by
    intro n m a a' hnm han ham
    have hstep : ι (a ^ q ^ (m - n)) = ι a' := by
      rw [map_pow, han, ← pow_mul, ← pow_add, ham]
      congr 2
      omega
    have haa' : a ^ q ^ (m - n) = a' := hι hstep
    have hga' : g a' = ((powMulEquiv q hq) : C → C)^[m - n] (g a) := by
      rw [← haa', map_pow, powMulEquiv_iterate]
    have h1 : m = n + (m - n) := by omega
    have hcancel : ((powMulEquiv q hq).symm : C → C)^[m]
          (((powMulEquiv q hq) : C → C)^[m - n] (g a))
        = ((powMulEquiv q hq).symm : C → C)^[n] (g a) := by
      calc ((powMulEquiv q hq).symm : C → C)^[m]
            (((powMulEquiv q hq) : C → C)^[m - n] (g a))
          = ((powMulEquiv q hq).symm : C → C)^[n + (m - n)]
            (((powMulEquiv q hq) : C → C)^[m - n] (g a)) := by rw [← h1]
        _ = ((powMulEquiv q hq).symm : C → C)^[n]
            (((powMulEquiv q hq).symm : C → C)^[m - n]
              (((powMulEquiv q hq) : C → C)^[m - n] (g a))) :=
            Function.iterate_add_apply _ _ _ _
        _ = ((powMulEquiv q hq).symm : C → C)^[n] (g a) := by
            congr 1
            exact Function.LeftInverse.iterate
              (fun c => (powMulEquiv q hq).symm_apply_apply c) (m - n) (g a)
    rw [hga', hcancel]
  rcases le_total n m with h | h
  · exact key n m a a' h han ham
  · exact (key m n a' a h ham han).symm

include hι hq in
/-- **Restriction along a `q`-radicial inclusion is surjective on characters.** -/
theorem charRestrict_surjective
    (hpow : ∀ b : B, ∃ (n : ℕ) (a : A), ι a = b ^ q ^ n) (g : A →* C) :
    ∃ f : B →* C, f.comp ι = g := by
  classical
  choose N aN hN using hpow
  have hraise : ∀ (b : B) (n k : ℕ) (a : A), n ≤ k → ι a = b ^ q ^ n →
      ι (a ^ q ^ (k - n)) = b ^ q ^ k := by
    intro b n k a hnk ha
    rw [map_pow, ha, ← pow_mul, ← pow_add]
    congr 2
    omega
  refine ⟨MonoidHom.mk'
      (fun b => ((powMulEquiv q hq).symm : C → C)^[N b] (g (aN b))) ?_, ?_⟩
  · intro b b'
    obtain ⟨k, hkb, hkb', hkbb'⟩ :
        ∃ k : ℕ, N b ≤ k ∧ N b' ≤ k ∧ N (b * b') ≤ k :=
      ⟨max (max (N b) (N b')) (N (b * b')),
        le_trans (le_max_left _ _) (le_max_left _ _),
        le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
    have hb : ι (aN b ^ q ^ (k - N b)) = b ^ q ^ k := hraise b (N b) k (aN b) hkb (hN b)
    have hb' : ι (aN b' ^ q ^ (k - N b')) = b' ^ q ^ k := hraise b' (N b') k (aN b') hkb' (hN b')
    have hbb' : ι (aN b ^ q ^ (k - N b) * aN b' ^ q ^ (k - N b'))
        = (b * b') ^ q ^ k := by rw [map_mul, hb, hb', mul_pow]
    have e1 : ((powMulEquiv q hq).symm : C → C)^[N b] (g (aN b))
        = ((powMulEquiv q hq).symm : C → C)^[k] (g (aN b ^ q ^ (k - N b))) :=
      charRoot_well_defined ι hι q hq g b (N b) k (aN b) _ (hN b) hb
    have e2 : ((powMulEquiv q hq).symm : C → C)^[N b'] (g (aN b'))
        = ((powMulEquiv q hq).symm : C → C)^[k] (g (aN b' ^ q ^ (k - N b'))) :=
      charRoot_well_defined ι hι q hq g b' (N b') k (aN b') _ (hN b') hb'
    have e3 : ((powMulEquiv q hq).symm : C → C)^[N (b * b')] (g (aN (b * b')))
        = ((powMulEquiv q hq).symm : C → C)^[k]
          (g (aN b ^ q ^ (k - N b) * aN b' ^ q ^ (k - N b'))) :=
      charRoot_well_defined ι hι q hq g (b * b') (N (b * b')) k (aN (b * b')) _
        (hN (b * b')) hbb'
    rw [e1, e2, e3, map_mul, powMulEquiv_symm_iterate_mul]
  · refine MonoidHom.ext fun a => ?_
    show ((powMulEquiv q hq).symm : C → C)^[N (ι a)] (g (aN (ι a))) = g a
    have ha : ι a = (ι a) ^ q ^ (0 : ℕ) := by simp
    have hres := charRoot_well_defined ι hι q hq g (ι a) (N (ι a)) 0 (aN (ι a)) a (hN (ι a)) ha
    simpa using hres

include hι hq in
/-- **Restriction along a `q`-radicial inclusion is a bijection on characters.** -/
theorem charRestrict_bijective
    (hpow : ∀ b : B, ∃ (n : ℕ) (a : A), ι a = b ^ q ^ n) :
    Function.Bijective (fun f : B →* C => f.comp ι) :=
  ⟨fun _ _ h => charRestrict_injective ι q hq.1 hpow h,
    fun g => charRestrict_surjective ι hι q hq hpow g⟩


end HTGeometry
