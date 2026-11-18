import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SplitInfinityRegulatorDomain
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Relative degree characters of a split regulator

Molla's Corollary 3.8 distinguishes 2R relative degree characters before
quotienting by norm twists and R after quotienting. The two individual
Laurent uniformizers detect both identifications. The principal-unit
components of the fundamental generator have no effect on this factor.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity
variable {F : Type*} [Field F]

/-- Independent phases on the relative degree and on the norm degree. -/
def relativePhase (z : Circle) (x : LocalUnit F × LocalUnit F) : Circle :=
  z^(degree x.1-degree x.2)

def normPhase (z : Circle) (x : LocalUnit F × LocalUnit F) : Circle :=
  z^(degree x.1+degree x.2)

theorem phase_on_translate (R : ℕ+) (u v : LocalUnit F) (w c : Fˣ)
    (x : LocalUnit F × LocalUnit F) (j : ℤ) (z : Circle) :
    relativePhase z (translate (generator R u v w) x c j) =
      relativePhase z x*(z^(2*(R : ℤ)))^j := by
  have hg := generator_invariants R u v w
  simp only [relativePhase,translate,degree_mul,degree_monomial,degree_pow,hg.1,hg.2.1,zero_add]
  rw [← zpow_mul,← zpow_add]
  congr 1
  ring

/-- Descent through all changes of fundamental generator is precisely a root of unity condition. -/
theorem relative_descends_iff (R : ℕ+) (u v : LocalUnit F) (w : Fˣ) (z : Circle) :
    (∀ (x : LocalUnit F × LocalUnit F) (c : Fˣ) (j : ℤ),
      relativePhase z (translate (generator R u v w) x c j)=relativePhase z x) ↔
      z^(2*(R : ℤ))=1 := by
  simp_rw [phase_on_translate]
  constructor
  · intro h
    simpa using h (u,v) 1 1
  · intro h x c j
    simp [h]

private def probes (a b : ℤ) : LocalUnit F × LocalUnit F :=
  (monomial 1 a,monomial 1 b)

/-- Two relative phases have the same norm-twist class exactly when their
ratio is a sign. A twist, if it exists, must be that very ratio. -/
theorem norm_twist_iff (z w t : Circle) :
    (∀ x : LocalUnit F × LocalUnit F, relativePhase z x = normPhase t x*relativePhase w x) ↔
      t=z/w ∧ t=t⁻¹ := by
  constructor
  · intro h
    have h₁ := h (probes (F := F) 1 0)
    have h₂ := h (probes (F := F) 0 1)
    simp only [probes,relativePhase,normPhase,degree_monomial,sub_zero,add_zero,zero_add,
      zero_sub,zpow_one,zpow_neg_one] at h₁ h₂
    have he := (eq_div_iff_mul_eq).2 h₁.symm
    refine ⟨he,?_⟩
    rw [h₁,mul_inv_rev] at h₂
    apply mul_left_cancel (a := w⁻¹)
    exact (by rw [mul_comm (w⁻¹) t]; exact h₂.symm)
  · rintro ⟨ht,hinv⟩ x
    have he : z=t*w := (eq_div_iff_mul_eq.mp ht).symm
    rw [he,relativePhase,relativePhase,normPhase,mul_zpow]
    congr 1
    rw [zpow_sub,zpow_add,div_eq_mul_inv,← inv_zpow,← hinv]

private instance modulus_neZero (R : ℕ+) : NeZero (2*(R : ℕ)) :=
  ⟨Nat.mul_ne_zero (by decide) R.pos.ne'⟩

/-- Frequency labeled on the period-2R lattice. -/
def indexedPhase (R : ℕ+) (n : ℤ) : Circle :=
  ZMod.toCircle (n : ZMod (2*(R : ℕ)))

/-- Every descending relative phase has exactly one frequency modulo 2R. -/
theorem unique_frequency_iff (R : ℕ+) (u v : LocalUnit F) (w : Fˣ) (z : Circle) :
    (∀ (x : LocalUnit F × LocalUnit F) (c : Fˣ) (j : ℤ),
      relativePhase z (translate (generator R u v w) x c j)=relativePhase z x) ↔
      ∃! k : ZMod (2*(R : ℕ)), ZMod.toCircle k = z := by
  let N := 2*(R : ℕ)
  have hc : 2*(R : ℤ) = (N : ℤ) := by simp [N]
  rw [relative_descends_iff,hc,zpow_natCast]
  constructor
  · intro h
    let ζ : rootsOfUnity N Circle := ⟨toUnits z,(mem_rootsOfUnity' _ _).2 h⟩
    obtain ⟨k,hk⟩ := (bijective_rootsOfUnityAddChar N).surjective ζ
    have he : ZMod.toCircle k = z := congrArg (fun t : rootsOfUnity N Circle => (t.val : Circle)) hk
    exact ⟨k,he,fun j hj => ZMod.injective_toCircle (hj.trans he.symm)⟩
  · rintro ⟨k,rfl,_⟩
    exact (mem_rootsOfUnity' _ _).1 (ZMod.rootsOfUnityAddChar N k).property

theorem indexed_equal_iff (R : ℕ+) (n m : ℤ) :
    (∀ x : LocalUnit F × LocalUnit F, relativePhase (indexedPhase R n) x =
      relativePhase (indexedPhase R m) x) ↔ (2*(R : ℤ)) ∣ m-n := by
  have equality : indexedPhase R n=indexedPhase R m ↔ (2*(R : ℤ)) ∣ m-n := by
    rw [indexedPhase,indexedPhase,ZMod.injective_toCircle.eq_iff,ZMod.intCast_eq_intCast_iff_dvd_sub]
    norm_cast
  constructor
  · intro h
    apply equality.1
    simpa [probes,relativePhase,degree_monomial] using h (probes (F := F) 1 0)
  · intro h x
    rw [equality.2 h]

private theorem indexed_div (R : ℕ+) (n m : ℤ) :
    indexedPhase R n/indexedPhase R m=indexedPhase R (n-m) := by
  simp [indexedPhase,AddChar.map_sub_eq_div]

private theorem indexed_inv (R : ℕ+) (n : ℤ) :
    (indexedPhase R n)⁻¹=indexedPhase R (-n) := by
  simp [indexedPhase]

/-- Quotienting by all norm-degree twists divides the arithmetic period by
exactly two. The two possible representatives differ by the norm parity. -/
theorem indexed_mod_norm (R : ℕ+) (n m : ℤ) :
    (∃ t : Circle, ∀ x : LocalUnit F × LocalUnit F,
      relativePhase (indexedPhase R n) x = normPhase t x * relativePhase (indexedPhase R m) x) ↔
      (R : ℤ) ∣ n-m := by
  simp_rw [norm_twist_iff (F := F),indexed_div]
  rw [exists_eq_left',indexed_inv,indexedPhase,indexedPhase,ZMod.injective_toCircle.eq_iff,
    ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨-a,by linarith only [ha]⟩
  · rintro ⟨a,ha⟩
    exact ⟨-a,by linarith only [ha]⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.phase_on_translate
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.relative_descends_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.norm_twist_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.unique_frequency_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.indexed_equal_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.indexed_mod_norm
