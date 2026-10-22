import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.RamificationInertia.Inertia

/-!
# Non-archimedean base change for adic absolute values

For a height-one prime `w` of the integers of `L` lying over `v` in the integers of `K`, the adic
absolute value of an element of `K` computed at `w` is its absolute value at `v` raised to the
local degree `e(w|v) · f(w|v)`: the valuation scales by the ramification index and the residue
norm — the base of the absolute value — is the `f`-th power of the residue norm at `v`.

* `deningerToNNReal_base_pow` : raising the base of `WithZeroMulInt.toNNReal` to a power raises
  the value to that power.
* `deningerAdicAbv_liesOver` : the local-degree scaling law.
-/

namespace RHTower

open NumberField IsDedekindDomain

section ToNNRealBase

/-- The value of `toNNReal` depends only on the base, not on the proof that it is nonzero. -/
theorem deningerToNNReal_congr {e e' : NNReal} (he : e ≠ 0) (he' : e' ≠ 0) (h : e = e')
    (x : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal he x = WithZeroMulInt.toNNReal he' x := by
  subst h
  rfl

/-- **Raising the base raises the value.**  `toNNReal` with base `e ^ f` is the `f`-th power of
`toNNReal` with base `e`. -/
theorem deningerToNNReal_base_pow {e : NNReal} (he : e ≠ 0) {f : ℕ} (hf : f ≠ 0)
    (hef : e ^ f ≠ 0) (x : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal hef x = (WithZeroMulInt.toNNReal he x) ^ f := by
  by_cases hx : x = 0
  · rw [WithZeroMulInt.toNNReal_pos_apply hef hx, WithZeroMulInt.toNNReal_pos_apply he hx,
      zero_pow hf]
  · rw [WithZeroMulInt.toNNReal_neg_apply hef hx, WithZeroMulInt.toNNReal_neg_apply he hx,
      ← zpow_natCast e f, ← zpow_mul,
      ← zpow_natCast (e ^ (Multiplicative.toAdd (WithZero.unzero hx))) f, ← zpow_mul, mul_comm]

end ToNNRealBase

section AdicAbvBaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- **The local-degree scaling law.**  For `x` in the base field, the adic absolute value at a
place `w` above `v` is the absolute value at `v` raised to the local degree `e · f`. -/
theorem deningerAdicAbv_liesOver (x : K) :
    HeightOneSpectrum.adicAbv L w (algebraMap K L x)
      = (HeightOneSpectrum.adicAbv K v x)
          ^ (v.asIdeal.ramificationIdx' w.asIdeal * v.asIdeal.inertiaDeg' w.asIdeal) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  set e := v.asIdeal.ramificationIdx' w.asIdeal with he
  set f := v.asIdeal.inertiaDeg' w.asIdeal with hfdef
  have hfne : f ≠ 0 := Ideal.inertiaDeg'_ne_zero v.asIdeal w.asIdeal
  have hnorm : ((Ideal.absNorm w.asIdeal : NNReal))
      = ((Ideal.absNorm v.asIdeal : NNReal)) ^ f := by
    rw [hfdef, ← Nat.cast_pow,
      Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot]
  have hbase : ((Ideal.absNorm v.asIdeal : NNReal)) ^ f ≠ 0 := by
    rw [← hnorm]
    exact HeightOneSpectrum.absNorm_ne_zero w
  have hval := HeightOneSpectrum.valuation_liesOver L v w x
  rw [HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.adicAbv_def, ← hval,
    deningerToNNReal_congr (HeightOneSpectrum.absNorm_ne_zero w) hbase hnorm,
    deningerToNNReal_base_pow (HeightOneSpectrum.absNorm_ne_zero v) hfne hbase, map_pow,
    ← NNReal.coe_pow, ← pow_mul]

end AdicAbvBaseChange

end RHTower
