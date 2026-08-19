import GaloisForLFunctions.HTGeometry.QuantumChannelDiamond

/-!
# Markovian return recovery and complexity reflection

A quantum dynamical semigroup is a one-parameter family of channels with `Λ₀ = id` and
`Λ_{s+t} = Λ_s ∘ Λ_t`.  If the full channel returns to the identity at time `R` up to diamond
defect `δ_R`, then:

* the remaining evolution `Λ_{R−t}` is an explicit `δ_R`-recovery for `Λ_t`, simultaneously at
  every intermediate time (Theorem A, `(6)`–`(7)`);
* no intermediate stage can lose more than a relative `δ_R` of any ancilla-assisted
  trace-norm distinguishability (Theorem A, `(8)`);
* inverse words reflect the whole approximate-circuit structure across the return, at radius
  shift `δ_R`, both for complexities and for exact-length incidence counts, and hence for every
  nonnegative length partition function (Theorem B, `(9)`–`(11)`).
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A quantum dynamical semigroup**: a one-parameter family of channels with `Λ₀ = id` and
`Λ_{s+t} = Λ_s ∘ Λ_t`.  No continuity is assumed. -/
structure DynamicalSemigroup (n : Type*) [Fintype n] [DecidableEq n] where
  /-- The channel at each time. -/
  ch : ℝ≥0 → QuantumChannel n
  /-- The channel at time zero is the identity. -/
  ch_zero : ch 0 = 1
  /-- The semigroup law. -/
  ch_add : ∀ s t : ℝ≥0, ch (s + t) = ch s * ch t

namespace DynamicalSemigroup

variable (S : DynamicalSemigroup n)

/-- **`(6)`, the recovery identity.**  The remaining evolution composed with the elapsed evolution
is the full return, in either order. -/
theorem recovery_left {t R : ℝ≥0} (h : t ≤ R) : S.ch (R - t) * S.ch t = S.ch R := by
  rw [← S.ch_add, tsub_add_cancel_of_le h]

theorem recovery_right {t R : ℝ≥0} (h : t ≤ R) : S.ch t * S.ch (R - t) = S.ch R := by
  rw [← S.ch_add, add_comm, tsub_add_cancel_of_le h]

/-- **`(7)`.**  The recovery defect of the pair is exactly the return defect. -/
theorem dist_recovery_eq {t R : ℝ≥0} (h : t ≤ R) :
    dist (S.ch (R - t) * S.ch t) 1 = dist (S.ch R) 1 := by
  rw [S.recovery_left h]

end DynamicalSemigroup

namespace QuantumChannel

theorem amplify_one (k : ℕ) (X : Matrix (n × Fin k) (n × Fin k) ℂ) :
    amplify (1 : QuantumChannel n).map (Fin k) X = X := by
  have h1 : (1 : QuantumChannel n).map = id := rfl
  rw [h1]
  rfl

/-- **The diamond distance to the identity controls the relative loss of trace norm.** -/
theorem nuclearNorm_sub_self_le (c : QuantumChannel n) (k : ℕ)
    (X : Matrix (n × Fin k) (n × Fin k) ℂ) :
    finiteMatrixNuclearNorm (amplify c.map (Fin k) X - X)
      ≤ diamondDist c 1 * finiteMatrixNuclearNorm X := by
  have h := nuclearNorm_sub_le_diamondDist_mul c 1 k X
  rwa [amplify_one] at h

end QuantumChannel

namespace DynamicalSemigroup

variable (S : DynamicalSemigroup n)

/-- **`(8)`.**  No intermediate stage of an approximate return loses more than the relative return
defect of any ancilla-assisted trace norm. -/
theorem one_sub_defect_mul_nuclearNorm_le {t R : ℝ≥0} (h : t ≤ R) (k : ℕ)
    (X : Matrix (n × Fin k) (n × Fin k) ℂ) :
    (1 - dist (S.ch R) 1) * finiteMatrixNuclearNorm X
      ≤ finiteMatrixNuclearNorm (amplify (S.ch t).map (Fin k) X) := by
  have hcomp : amplify (S.ch R).map (Fin k) X
      = amplify (S.ch (R - t)).map (Fin k) (amplify (S.ch t).map (Fin k) X) := by
    rw [← QuantumChannel.amplify_mul, S.recovery_left h]
  have h1 : finiteMatrixNuclearNorm (amplify (S.ch R).map (Fin k) X)
      ≤ finiteMatrixNuclearNorm (amplify (S.ch t).map (Fin k) X) := by
    rw [hcomp]
    exact (S.ch (R - t)).nuclearNorm_amplify_le (Fin k) _
  have h2 : finiteMatrixNuclearNorm X
      - finiteMatrixNuclearNorm (amplify (S.ch R).map (Fin k) X)
      ≤ finiteMatrixNuclearNorm (amplify (S.ch R).map (Fin k) X - X) :=
    finiteMatrixNuclearNorm_sub_le_sub X (amplify (S.ch R).map (Fin k) X)
  have h3 := (S.ch R).nuclearNorm_sub_self_le k X
  have hd : dist (S.ch R) 1 = QuantumChannel.diamondDist (S.ch R) 1 := rfl
  rw [hd]
  nlinarith [h1, h2, h3]

end DynamicalSemigroup

/-! ## Theorem B: reflection across the return -/

/-- **A finite inverse-closed dictionary of unitary channels.** -/
structure UnitaryDictionary (n : Type*) [Fintype n] [DecidableEq n]
    (W : Type*) [Fintype W] [DecidableEq W] where
  /-- The channel realised by a word. -/
  word : W → QuantumChannel n
  /-- Word inversion. -/
  inv : W → W
  /-- Every word is a unitary channel. -/
  unitary_word : ∀ w : W, ∃ U : Matrix n n ℂ, ∃ hU : U ∈ unitary (Matrix n n ℂ),
    word w = QuantumChannel.unitaryChannel hU
  /-- Inversion inverts. -/
  inv_word : ∀ w : W, word (inv w) * word w = 1
  /-- Inversion is injective, hence a length-preserving bijection of the dictionary. -/
  inv_injective : Function.Injective inv

namespace UnitaryDictionary

variable {W : Type*} [Fintype W] [DecidableEq W] (D : UnitaryDictionary n W)

/-- Right composition by a dictionary word is a diamond isometry. -/
theorem dist_mul_word (w : W) (a b : QuantumChannel n) :
    dist (a * D.word w) (b * D.word w) = dist a b := by
  obtain ⟨U, hU, hw⟩ := D.unitary_word w
  rw [hw]
  exact QuantumChannel.diamondDist_mul_unitaryChannel a b hU

/-- **`(9)`, complexity reflection.**  A dictionary word realising `T` at radius `ε` realises the
recovery `S` at radius `ε + δ` after inversion. -/
theorem dist_reflect_word {S T : QuantumChannel n} {w : W} {δ ε : ℝ}
    (hret : dist (S * T) 1 ≤ δ) (hW : dist (D.word w) T ≤ ε) :
    dist S (D.word (D.inv w)) ≤ ε + δ :=
  dist_reflect_le QuantumChannel.leftContracting_quantumChannel (D.dist_mul_word w) (D.inv_word w) hret hW

/-- **`(10)`, incidence reflection.**  At each exact word length the reflection is injective, so
the incidence counts interlace at radius shift `δ`. -/
theorem card_reflect_word {S T : QuantumChannel n} {δ ε : ℝ}
    (hret : dist (S * T) 1 ≤ δ) :
    (Finset.univ.filter fun w : W => dist (D.word w) T ≤ ε).card
      ≤ (Finset.univ.filter fun w : W => dist (D.word w) S ≤ ε + δ).card :=
  card_reflect_le D.word D.inv QuantumChannel.leftContracting_quantumChannel hret
    (fun w => D.dist_mul_word w) D.inv_word D.inv_injective

end UnitaryDictionary

/-- **`(11)`, the partition-function form.**  Any nonnegative weighting of the interlacing
incidence counts interlaces. -/
theorem sum_weighted_le {ι : Type*} (s : Finset ι) (b I J : ι → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i) (h : ∀ i ∈ s, I i ≤ J i) :
    ∑ i ∈ s, b i * I i ≤ ∑ i ∈ s, b i * J i :=
  Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) (hb i hi)

/-- **Theorem B for a dynamical semigroup.**  With `δ_R` the return defect, every dictionary word
approximating `Λ_t` at radius `ε` has its inverse approximating `Λ_{R−t}` at radius `ε + δ_R`. -/
theorem DynamicalSemigroup.dist_reflect_word {W : Type*} [Fintype W] [DecidableEq W]
    (S : DynamicalSemigroup n) (D : UnitaryDictionary n W) {t R : ℝ≥0} (h : t ≤ R) {w : W}
    {ε : ℝ} (hW : dist (D.word w) (S.ch t) ≤ ε) :
    dist (S.ch (R - t)) (D.word (D.inv w)) ≤ ε + dist (S.ch R) 1 :=
  D.dist_reflect_word (le_of_eq (S.dist_recovery_eq h)) hW

/-- **Theorem B, incidence form, for a dynamical semigroup.** -/
theorem DynamicalSemigroup.card_reflect_word {W : Type*} [Fintype W] [DecidableEq W]
    (S : DynamicalSemigroup n) (D : UnitaryDictionary n W) {t R : ℝ≥0} (h : t ≤ R) {ε : ℝ} :
    (Finset.univ.filter fun w : W => dist (D.word w) (S.ch t) ≤ ε).card
      ≤ (Finset.univ.filter fun w : W =>
          dist (D.word w) (S.ch (R - t)) ≤ ε + dist (S.ch R) 1).card :=
  D.card_reflect_word (le_of_eq (S.dist_recovery_eq h))

end

end GaloisForLFunctions.HTGeometry
