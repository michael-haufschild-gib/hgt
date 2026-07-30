import GaloisForLFunctions.HTGeometry.SourceOrderedPairComplexStructure

/-!
# Projective source visibility and successor parity

If two linear source changes have a nontrivial scalar commutator, no nonzero vector is fixed by
both. Their two individually lossy defect reports are therefore jointly injective. For the
standard binary source pair, the same sign obstruction generates an ordered square of `-1` and
makes the joint defect reporter injective exactly on odd symmetric-successor degrees.

This is elementary projective-representation and Clifford algebra. It does not identify physical
states or derive quantum probability, time, spacetime, gravity, or gauge forces.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Difference between a vector and its image under one linear source change. -/
def sourceChangeDefect (A : V →ₗ[K] V) : V →ₗ[K] V :=
  LinearMap.id - A

/-- The paired defect fingerprint of two source changes. -/
def projectiveSourceJointDefect (A B : V →ₗ[K] V) : V →ₗ[K] V × V :=
  (sourceChangeDefect A).prod (sourceChangeDefect B)

/-- A nontrivial scalar commutator forbids a nonzero common fixed vector. -/
theorem eq_zero_of_projective_source_fixed
    (A B : V →ₗ[K] V) (ζ : K)
    (hcomm : A.comp B = ζ • (B.comp A))
    (hζ : ζ ≠ 1) (v : V)
    (hA : A v = v) (hB : B v = v) :
    v = 0 := by
  have hpoint := LinearMap.congr_fun hcomm v
  have hv : v = ζ • v := by
    calc
      v = A (B v) := by rw [hB, hA]
      _ = ζ • B (A v) := by simpa using hpoint
      _ = ζ • v := by rw [hA, hB]
  have hscalar : (1 - ζ) • v = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero.mpr hv
  have hnonzero : 1 - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ)
  exact (smul_eq_zero.mp hscalar).resolve_left hnonzero

/-- **Scalar-cocycle visibility law.** If `A B = ζ B A` with `ζ ≠ 1`, the two source-defect
reports are jointly injective. -/
theorem projectiveSourceJointDefect_injective
    (A B : V →ₗ[K] V) (ζ : K)
    (hcomm : A.comp B = ζ • (B.comp A))
    (hζ : ζ ≠ 1) :
    Function.Injective (projectiveSourceJointDefect A B) := by
  rw [← LinearMap.ker_eq_bot]
  ext v
  constructor
  · intro hv
    have hpair : (sourceChangeDefect A v, sourceChangeDefect B v) = (0, 0) := by
      simpa [projectiveSourceJointDefect] using hv
    have hA : A v = v := by
      have hfirst := congrArg Prod.fst hpair
      exact (sub_eq_zero.mp (by simpa [sourceChangeDefect] using hfirst)).symm
    have hB : B v = v := by
      have hsecond := congrArg Prod.snd hpair
      exact (sub_eq_zero.mp (by simpa [sourceChangeDefect] using hsecond)).symm
    exact eq_zero_of_projective_source_fixed A B ζ hcomm hζ v hA hB
  · intro hv
    have hv0 : v = 0 := by simpa using hv
    subst v
    simp [projectiveSourceJointDefect, sourceChangeDefect]

/-- Anticommuting involutions generate an ordered operator whose square is minus the identity. -/
theorem orderedProduct_sq_neg_one_of_anticommute
    (J S : V →ₗ[K] V)
    (hJ : J.comp J = LinearMap.id)
    (hS : S.comp S = LinearMap.id)
    (hcomm : J.comp S = -(S.comp J)) :
    (J.comp S).comp (J.comp S) = -LinearMap.id := by
  ext v
  have hpoint : J (S v) = -S (J v) := by
    simpa using LinearMap.congr_fun hcomm v
  have hJpoint : J (J v) = v := by
    simpa using LinearMap.congr_fun hJ v
  have hSpoint : S (S (J v)) = J v := by
    simpa using LinearMap.congr_fun hS (J v)
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply]
  calc
    J (S (J (S v))) = J (S (-S (J v))) := by rw [hpoint]
    _ = -J (S (S (J v))) := by simp
    _ = -J (J v) := by rw [hSpoint]
    _ = -v := by rw [hJpoint]

/-- For involutions, an ordered square of minus the identity recovers anticommutation. -/
theorem anticommute_of_orderedProduct_sq_neg_one
    (J S : V →ₗ[K] V)
    (hJ : J.comp J = LinearMap.id)
    (hS : S.comp S = LinearMap.id)
    (hI : (J.comp S).comp (J.comp S) = -LinearMap.id) :
    J.comp S = -(S.comp J) := by
  apply LinearMap.ext
  intro v
  have hIpoint := LinearMap.congr_fun hI (S v)
  have hSpoint : S (S v) = v := by
    simpa using LinearMap.congr_fun hS v
  have hJpoint : J (J (S (J v))) = S (J v) := by
    simpa using LinearMap.congr_fun hJ (S (J v))
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply] at hIpoint ⊢
  rw [hSpoint] at hIpoint
  have happly := congrArg J hIpoint
  simp only [map_neg] at happly
  rw [hJpoint] at happly
  simpa using (congrArg Neg.neg happly).symm

/-- Source polarity on coefficient arrays of degree-`n` homogeneous binary forms. Coordinate
`i` is the coefficient whose second-variable exponent is `i`. -/
def binaryFormSourcePolarity (n : ℕ) :
    (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K) where
  toFun a i := (-1 : K) ^ i.val * a i
  map_add' a b := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c a := by
    funext i
    change (-1 : K) ^ i.val * (c * a i) =
      c * ((-1 : K) ^ i.val * a i)
    ring

/-- Exchange of the two binary-form variables, represented by coefficient reversal. -/
def binaryFormSourceSwap (n : ℕ) :
    (Fin (n + 1) → K) →ₗ[K] (Fin (n + 1) → K) where
  toFun a i := a (Fin.rev i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- On every odd symmetric-successor degree, source polarity and source exchange anticommute. -/
theorem binaryFormSource_anticommute_of_odd
    (n : ℕ) (hn : Odd n) :
    (binaryFormSourcePolarity (K := K) n).comp
        (binaryFormSourceSwap (K := K) n) =
      -((binaryFormSourceSwap (K := K) n).comp
        (binaryFormSourcePolarity (K := K) n)) := by
  apply LinearMap.ext
  intro a
  funext i
  have hsum : i.val + (Fin.rev i).val = n := by
    simp [Fin.rev]
    omega
  have hpows :
      (-1 : K) ^ i.val * (-1 : K) ^ (Fin.rev i).val = -1 := by
    rw [← pow_add, hsum, hn.neg_one_pow]
  change
    (-1 : K) ^ i.val * a (Fin.rev i) =
      -((-1 : K) ^ (Fin.rev i).val * a (Fin.rev i))
  obtain hrev | hrev := neg_one_pow_eq_or K (Fin.rev i).val
  ·
    rw [hrev] at hpows ⊢
    simpa using congrArg (fun c : K => c * a (Fin.rev i)) hpows
  ·
    rw [hrev] at hpows ⊢
    have hsign : (-1 : K) ^ i.val = 1 := by
      simpa using hpows
    rw [hsign]
    simp

/-- Odd-degree homogeneous binary forms are recovered by the two individually lossy source
defects. -/
theorem binaryFormJointDefect_injective_of_odd
    [CharZero K] (n : ℕ) (hn : Odd n) :
    Function.Injective
      (projectiveSourceJointDefect
        (binaryFormSourcePolarity (K := K) n)
        (binaryFormSourceSwap (K := K) n)) := by
  apply projectiveSourceJointDefect_injective
    (K := K) (V := Fin (n + 1) → K)
    (binaryFormSourcePolarity (K := K) n)
    (binaryFormSourceSwap (K := K) n) (-1 : K)
  · calc
      (binaryFormSourcePolarity (K := K) n).comp
          (binaryFormSourceSwap (K := K) n) =
        -((binaryFormSourceSwap (K := K) n).comp
          (binaryFormSourcePolarity (K := K) n)) :=
            binaryFormSource_anticommute_of_odd (K := K) n hn
      _ = (-1 : K) •
          ((binaryFormSourceSwap (K := K) n).comp
            (binaryFormSourcePolarity (K := K) n)) := by
              apply LinearMap.ext
              intro a
              funext i
              simp
  · norm_num

/-- The binary-form sector `x^n + y^n`, represented by its two endpoint coefficients. -/
def binaryFormEndpointSector (n : ℕ) : Fin (n + 1) → K :=
  fun i => if i.val = 0 ∨ i.val = n then 1 else 0

/-- The endpoint sector is nonzero at every degree. -/
theorem binaryFormEndpointSector_ne_zero (n : ℕ) :
    binaryFormEndpointSector (K := K) n ≠ 0 := by
  intro h
  have hzero := congrFun h (0 : Fin (n + 1))
  simp [binaryFormEndpointSector] at hzero

/-- At even degree the endpoint sector is fixed by source polarity. -/
theorem binaryFormEndpointSector_fixed_polarity
    (n : ℕ) (hn : Even n) :
    binaryFormSourcePolarity (K := K) n
        (binaryFormEndpointSector (K := K) n) =
      binaryFormEndpointSector (K := K) n := by
  funext i
  by_cases hi0 : i.val = 0
  · simp [binaryFormSourcePolarity, binaryFormEndpointSector, hi0]
  by_cases hin : i.val = n
  · simp [binaryFormSourcePolarity, binaryFormEndpointSector, hin,
      hn.neg_one_pow]
  · simp [binaryFormSourcePolarity, binaryFormEndpointSector, hi0, hin]

/-- The endpoint sector is fixed by source exchange at every degree. -/
theorem binaryFormEndpointSector_fixed_swap (n : ℕ) :
    binaryFormSourceSwap (K := K) n
        (binaryFormEndpointSector (K := K) n) =
      binaryFormEndpointSector (K := K) n := by
  funext i
  change
    (if (Fin.rev i).val = 0 ∨ (Fin.rev i).val = n then 1 else 0) =
      (if i.val = 0 ∨ i.val = n then 1 else 0)
  by_cases hi0 : i.val = 0
  · have hirevn : (Fin.rev i).val = n := by
      simp [Fin.rev]
      omega
    rw [if_pos (Or.inr hirevn), if_pos (Or.inl hi0)]
  by_cases hin : i.val = n
  · have hirev0 : (Fin.rev i).val = 0 := by
      simp [Fin.rev]
      omega
    rw [if_pos (Or.inl hirev0), if_pos (Or.inr hin)]
  · have hirev0 : (Fin.rev i).val ≠ 0 := by
      simp [Fin.rev]
      omega
    have hirevn : (Fin.rev i).val ≠ n := by
      simp [Fin.rev]
      omega
    rw [if_neg (not_or_intro hirev0 hirevn),
      if_neg (not_or_intro hi0 hin)]

/-- Every even symmetric-successor degree has an explicit nonzero sector invisible to both source
defects. -/
theorem binaryFormJointDefect_not_injective_of_even
    (n : ℕ) (hn : Even n) :
    ¬ Function.Injective
      (projectiveSourceJointDefect
        (binaryFormSourcePolarity (K := K) n)
        (binaryFormSourceSwap (K := K) n)) := by
  intro hinjective
  let w := binaryFormEndpointSector (K := K) n
  have hw : w ≠ 0 := binaryFormEndpointSector_ne_zero n
  have hJ :
      binaryFormSourcePolarity (K := K) n w = w :=
    binaryFormEndpointSector_fixed_polarity n hn
  have hS :
      binaryFormSourceSwap (K := K) n w = w :=
    binaryFormEndpointSector_fixed_swap n
  apply hw
  apply hinjective
  simp [projectiveSourceJointDefect, sourceChangeDefect, hJ, hS]

/-- **Exact successor-visibility parity law.** The paired source defects recover a homogeneous
binary form exactly at odd degree. -/
theorem binaryFormJointDefect_injective_iff_odd
    [CharZero K] (n : ℕ) :
    Function.Injective
        (projectiveSourceJointDefect
          (binaryFormSourcePolarity (K := K) n)
          (binaryFormSourceSwap (K := K) n)) ↔
      Odd n := by
  constructor
  · intro hinjective
    by_contra hn
    exact binaryFormJointDefect_not_injective_of_even n
      (Nat.not_odd_iff_even.mp hn) hinjective
  · exact binaryFormJointDefect_injective_of_odd n

end

end GaloisForLFunctions.HTGeometry
