import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Minimum

/-! # Independent spectral offsets on disjoint prime supports -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold.Composition

open Finset
open _root_.HTGeometry (supportedOccupationEquiv)

variable {S T : Finset Nat.Primes}

private theorem vanishes {P : Finset Nat.Primes} (a : P → ℕ) {p : Nat.Primes} (hp : p ∉ P) :
    ((supportedOccupationEquiv P) a).val p = 0 :=
  Finsupp.notMem_support_iff.mp fun h => hp (((supportedOccupationEquiv P) a).property h)

/-- Equality of joint energies determines the entire occupation of each disjoint factor. -/
theorem joint_energy_injective (hd : Disjoint S T) (a a' : S → ℕ) (b b' : T → ℕ) :
    energy (integerLabel S a)+energy (integerLabel T b) =
      energy (integerLabel S a')+energy (integerLabel T b') ↔ a=a' ∧ b=b' := by
  constructor
  · intro he
    rw [← energy_mul,← energy_mul] at he
    have invert (k : ℕ+) : Real.exp (energy k) = (k : ℕ) := Real.exp_log (Nat.cast_pos.mpr k.pos)
    have logs := congrArg Real.exp he
    rw [invert,invert] at logs
    have h := PNat.coe_injective (Nat.cast_injective (R := ℝ) logs)
    unfold integerLabel at h
    rw [← label_add,← label_add,label.injective.eq_iff] at h
    have hs : ((supportedOccupationEquiv S) a).val = ((supportedOccupationEquiv S) a').val := by
      ext p
      by_cases hp : p ∈ S
      · have hn := disjoint_left.mp hd hp
        have eq := DFunLike.congr_fun h p
        simpa only [Finsupp.add_apply,vanishes b hn,vanishes b' hn,add_zero] using eq
      · rw [vanishes a hp,vanishes a' hp]
    rw [hs] at h
    exact ⟨(supportedOccupationEquiv S).injective (Subtype.ext hs),
      (supportedOccupationEquiv T).injective (Subtype.ext (add_left_cancel h))⟩
  · rintro ⟨rfl,rfl⟩; rfl

variable {c : S → ℕ} {d : T → ℕ} {m n : ℕ}

/-- A lower and an upper joint excitation agree only if their two component offsets agree. -/
theorem match_components (hd : Disjoint S T) {a b u v : ℝ}
    (ha : a ∈ lowerEdge c m) (hb : b ∈ lowerEdge d n)
    (hu : u ∈ upperEdge c m) (hv : v ∈ upperEdge d n) (he : a+b=u+v) : a=u ∧ b=v := by
  obtain ⟨x,rfl⟩ := ha
  obtain ⟨y,rfl⟩ := hb
  obtain ⟨x',rfl⟩ := hu
  obtain ⟨y',rfl⟩ := hv
  obtain ⟨g,k,_,_,lo,hi,_⟩ := anchors x
  obtain ⟨f,j,_,_,lo',hi',_⟩ := anchors y
  simp only [lo,hi,lo',hi'] at he ⊢
  have eq : (energy (level x)+energy (level x'))+(energy (level y)+energy (level y')) =
      (energy (level g)+energy (level k))+(energy (level f)+energy (level j)) := by linarith only [he]
  simp only [level] at eq
  have pair {P : Finset Nat.Primes} (a b : P → ℕ) : energy (integerLabel P (a+b)) =
      energy (integerLabel P a)+energy (integerLabel P b) := by rw [integerLabel_add,energy_mul]
  have counts := (joint_energy_injective hd (count x+count x') (count g+count k)
    (count y+count y') (count f+count j)).mp (by simpa only [pair] using eq)
  have left := (energy_pair_iff g k x x').mpr (congrFun counts.1)
  have right := (energy_pair_iff f j y y').mpr (congrFun counts.2)
  constructor <;> linarith only [left,right]

def sums (A B : Set ℝ) := {z | ∃ x ∈ A, ∃ y ∈ B, x+y=z}

/-- Intersecting the lower and upper product edges pairs the two factors separately. -/
theorem shared_offsets (hd : Disjoint S T) :
    sums (lowerEdge c m) (lowerEdge d n) ∩ sums (upperEdge c m) (upperEdge d n) =
      sums (lowerEdge c m ∩ upperEdge c m) (lowerEdge d n ∩ upperEdge d n) := by
  ext z
  constructor
  · rintro ⟨⟨a,ha,b,hb,rfl⟩,u,hu,v,hv,he⟩
    obtain ⟨rfl,rfl⟩ := match_components hd ha hb hu hv he.symm
    exact ⟨_,⟨ha,hu⟩,_,⟨hb,hv⟩,rfl⟩
  · rintro ⟨a,⟨ha,hu⟩,b,⟨hb,hv⟩,rfl⟩
    exact ⟨⟨a,ha,b,hb,rfl⟩,a,hu,b,hv,rfl⟩

#print axioms joint_energy_injective
#print axioms match_components
#print axioms shared_offsets

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold.Composition
