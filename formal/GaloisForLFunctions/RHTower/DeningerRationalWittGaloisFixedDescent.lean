import GaloisForLFunctions.RHTower.DeningerRationalWittCyclotomicExhaustion

namespace RHTower

noncomputable section

/-- Absolute Galois action on the complexified arithmetic-closure monoid algebra. -/
noncomputable def deningerPrimeComplexifiedRationalWittGaloisAction
    (p : Nat.Primes) (g : DeningerPrimeArithmeticGalois p) :
    DeningerPrimeComplexifiedRationalWittPresentation p ≃ₐ[ℂ]
      DeningerPrimeComplexifiedRationalWittPresentation p :=
  MonoidAlgebra.domCongr ℂ ℂ
    (Units.mapEquiv g.toRingEquiv.toMulEquiv)

@[simp] theorem deningerPrimeComplexifiedRationalWittGaloisAction_single
    (p : Nat.Primes) (g : DeningerPrimeArithmeticGalois p)
    (x : (DeningerPrimeArithmeticClosure p)ˣ) (c : ℂ) :
    deningerPrimeComplexifiedRationalWittGaloisAction p g (MonoidAlgebra.single x c) =
      MonoidAlgebra.single (Units.mapEquiv g.toRingEquiv.toMulEquiv x) c := by
  simp [deningerPrimeComplexifiedRationalWittGaloisAction]

theorem deningerPrimeComplexifiedRationalWittGaloisAction_frobenius
    (p : Nat.Primes) :
    deningerPrimeComplexifiedRationalWittGaloisAction p (deningerPrimeArithmeticFrobenius p) =
      deningerPrimeComplexifiedRationalWittFrobenius p := by
  rfl

theorem deningerPrimeArithmeticGalois_exists_frobeniusPow_eq_on
    (p : Nat.Primes) (g : DeningerPrimeArithmeticGalois p)
    (a : DeningerPrimeArithmeticClosure p) :
    ∃ n : ℕ,
      g a = ((deningerPrimeArithmeticFrobenius p) ^ n) a := by
  let L := IntermediateField.adjoin (ZMod (p : ℕ)) ({a} : Set _)
  letI : FiniteDimensional (ZMod (p : ℕ)) L :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral a)
  letI : Finite L := Module.finite_of_finite (ZMod (p : ℕ))
  let r := AlgEquiv.restrictNormalHom
    (F := ZMod (p : ℕ)) (K₁ := DeningerPrimeArithmeticClosure p) L
  obtain ⟨m, hm⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
      (ZMod (p : ℕ)) L).surjective (r g)
  have hrf : r (deningerPrimeArithmeticFrobenius p) =
      FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod (p : ℕ)) L := by
    ext x
    calc
      ((r (deningerPrimeArithmeticFrobenius p) x : L)) =
          deningerPrimeArithmeticFrobenius p (x : _) :=
        AlgEquiv.restrictNormal_commutes _ L x
      _ = (x : DeningerPrimeArithmeticClosure p) ^
          Fintype.card (ZMod (p : ℕ)) := rfl
      _ = ((FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod (p : ℕ)) L) x : L) := rfl
  refine ⟨(m : ℕ), ?_⟩
  have hres : r ((deningerPrimeArithmeticFrobenius p) ^ (m : ℕ)) = r g := by
    rw [map_pow, hrf]
    exact hm
  let aL : L := IntermediateField.AdjoinSimple.gen (ZMod (p : ℕ)) a
  have ha := DFunLike.congr_fun hres aL
  have haL : (aL : DeningerPrimeArithmeticClosure p) = a := rfl
  have hgcomm := AlgEquiv.restrictNormal_commutes g L aL
  have hfcomm := AlgEquiv.restrictNormal_commutes
    ((deningerPrimeArithmeticFrobenius p) ^ (m : ℕ)) L aL
  calc
    g a = g (aL : DeningerPrimeArithmeticClosure p) := congrArg g haL.symm
    _ = ((r g aL : L) : DeningerPrimeArithmeticClosure p) := hgcomm.symm
    _ = ((r ((deningerPrimeArithmeticFrobenius p) ^ (m : ℕ)) aL : L) :
        DeningerPrimeArithmeticClosure p) :=
      congrArg (fun z : L => (z : DeningerPrimeArithmeticClosure p)) ha.symm
    _ = ((deningerPrimeArithmeticFrobenius p) ^ (m : ℕ))
        (aL : DeningerPrimeArithmeticClosure p) := hfcomm
    _ = ((deningerPrimeArithmeticFrobenius p) ^ (m : ℕ)) a := congrArg _ haL

theorem deningerPrimeArithmeticGalois_exists_frobeniusPow_eq_on_finiteFamily
    (p : Nat.Primes) (g : DeningerPrimeArithmeticGalois p)
    {ι : Type} [Finite ι] (a : ι → DeningerPrimeArithmeticClosure p) :
    ∃ n : ℕ, ∀ i,
      g (a i) = ((deningerPrimeArithmeticFrobenius p) ^ n) (a i) := by
  let S : Set (DeningerPrimeArithmeticClosure p) := Set.range a
  letI : Finite S := Set.finite_range a
  let L := IntermediateField.adjoin (ZMod (p : ℕ)) S
  letI : FiniteDimensional (ZMod (p : ℕ)) L :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  letI : Finite L := Module.finite_of_finite (ZMod (p : ℕ))
  let r := AlgEquiv.restrictNormalHom
    (F := ZMod (p : ℕ)) (K₁ := DeningerPrimeArithmeticClosure p) L
  obtain ⟨m, hm⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
      (ZMod (p : ℕ)) L).surjective (r g)
  have hrf : r (deningerPrimeArithmeticFrobenius p) =
      FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod (p : ℕ)) L := by
    ext x
    calc
      ((r (deningerPrimeArithmeticFrobenius p) x : L)) =
          deningerPrimeArithmeticFrobenius p (x : _) :=
        AlgEquiv.restrictNormal_commutes _ L x
      _ = (x : DeningerPrimeArithmeticClosure p) ^
          Fintype.card (ZMod (p : ℕ)) := rfl
      _ = ((FiniteField.frobeniusAlgEquivOfAlgebraic
          (ZMod (p : ℕ)) L) x : L) := rfl
  have hres : r ((deningerPrimeArithmeticFrobenius p) ^ (m : ℕ)) = r g := by
    rw [map_pow, hrf]
    exact hm
  refine ⟨(m : ℕ), fun i => ?_⟩
  let aiL : L :=
    ⟨a i, IntermediateField.subset_adjoin (ZMod (p : ℕ)) S ⟨i, rfl⟩⟩
  have hai := DFunLike.congr_fun hres aiL
  have hgcomm := AlgEquiv.restrictNormal_commutes g L aiL
  have hfcomm := AlgEquiv.restrictNormal_commutes
    ((deningerPrimeArithmeticFrobenius p) ^ (m : ℕ)) L aiL
  calc
    g (a i) = g (aiL : DeningerPrimeArithmeticClosure p) := rfl
    _ = ((r g aiL : L) : DeningerPrimeArithmeticClosure p) := hgcomm.symm
    _ = ((r ((deningerPrimeArithmeticFrobenius p) ^ (m : ℕ)) aiL : L) :
        DeningerPrimeArithmeticClosure p) :=
      congrArg (fun z : L => (z : DeningerPrimeArithmeticClosure p)) hai.symm
    _ = ((deningerPrimeArithmeticFrobenius p) ^ (m : ℕ))
        (aiL : DeningerPrimeArithmeticClosure p) := hfcomm
    _ = ((deningerPrimeArithmeticFrobenius p) ^ (m : ℕ)) (a i) := rfl

theorem deningerPrimeComplexifiedRationalWittGalois_eq_frobeniusPow_on_finiteStage
    (p : Nat.Primes) (g : DeningerPrimeArithmeticGalois p)
    (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    ∃ n : ℕ,
      ∀ v : DeningerFiniteCyclotomicWittAlgebra s.modulus,
        deningerPrimeComplexifiedRationalWittGaloisAction p g
            (deningerPrimeFiniteCyclotomicWittInclusion p s v) =
          deningerPrimeComplexifiedRationalWittGaloisAction p ((deningerPrimeArithmeticFrobenius p) ^ n)
            (deningerPrimeFiniteCyclotomicWittInclusion p s v) := by
  obtain ⟨n, hn⟩ := deningerPrimeArithmeticGalois_exists_frobeniusPow_eq_on_finiteFamily p g
    (fun j : Multiplicative (ZMod s.modulus) =>
      ((deningerPrimeFiniteWittRootEmbedding p s j :
        (DeningerPrimeArithmeticClosure p)ˣ) :
          DeningerPrimeArithmeticClosure p))
  refine ⟨n, fun v => ?_⟩
  induction v using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add j c w _hj _hc ih =>
      simp only [map_add]
      rw [ih]
      congr 1
      simp only [deningerPrimeFiniteCyclotomicWittInclusion_single,
        deningerPrimeComplexifiedRationalWittGaloisAction_single]
      have hunit :
          Units.mapEquiv g.toRingEquiv.toMulEquiv
              (deningerPrimeFiniteWittRootEmbedding p s
                (Multiplicative.ofAdd j)) =
            Units.mapEquiv
                ((deningerPrimeArithmeticFrobenius p) ^ n).toRingEquiv.toMulEquiv
              (deningerPrimeFiniteWittRootEmbedding p s
                (Multiplicative.ofAdd j)) := by
        apply Units.ext
        exact hn (Multiplicative.ofAdd j)
      rw [hunit]

theorem deningerPrimeComplexifiedRationalWittGaloisAction_mul_apply
    (p : Nat.Primes) (g h : DeningerPrimeArithmeticGalois p)
    (w : DeningerPrimeComplexifiedRationalWittPresentation p) :
    deningerPrimeComplexifiedRationalWittGaloisAction p (g * h) w =
      deningerPrimeComplexifiedRationalWittGaloisAction p g (deningerPrimeComplexifiedRationalWittGaloisAction p h w) := by
  induction w using MonoidAlgebra.induction with
  | zero => simp
  | single_add x c w _hx _hc ih =>
      simp only [map_add, ih]
      simp only [deningerPrimeComplexifiedRationalWittGaloisAction_single]
      have hunit :
          Units.mapEquiv (g * h).toRingEquiv.toMulEquiv x =
            Units.mapEquiv g.toRingEquiv.toMulEquiv
              (Units.mapEquiv h.toRingEquiv.toMulEquiv x) := by
        apply Units.ext
        rfl
      rw [hunit]

theorem deningerPrimeComplexifiedRationalWittGaloisAction_one_apply
    (p : Nat.Primes) (w : DeningerPrimeComplexifiedRationalWittPresentation p) :
    deningerPrimeComplexifiedRationalWittGaloisAction p 1 w = w := by
  induction w using MonoidAlgebra.induction with
  | zero => simp
  | single_add x c w _hx _hc ih =>
      simp only [map_add, ih, deningerPrimeComplexifiedRationalWittGaloisAction_single]
      have hunit : Units.mapEquiv (1 : DeningerPrimeArithmeticGalois p).toRingEquiv.toMulEquiv x = x := by
        apply Units.ext
        rfl
      rw [hunit]

theorem deningerPrimeComplexifiedRationalWittGaloisAction_frobeniusPow_fixed
    (p : Nat.Primes) (w : DeningerPrimeComplexifiedRationalWittPresentation p)
    (hw : deningerPrimeComplexifiedRationalWittFrobenius p w = w) :
    ∀ n : ℕ,
      deningerPrimeComplexifiedRationalWittGaloisAction p ((deningerPrimeArithmeticFrobenius p) ^ n) w = w := by
  intro n
  induction n with
  | zero => exact deningerPrimeComplexifiedRationalWittGaloisAction_one_apply p w
  | succ n ih =>
      rw [pow_succ, deningerPrimeComplexifiedRationalWittGaloisAction_mul_apply]
      rw [deningerPrimeComplexifiedRationalWittGaloisAction_frobenius]
      rw [hw]
      exact ih

theorem deningerPrimeComplexifiedRationalWittPresentation_frobenius_fixed_iff_galois_fixed
    (p : Nat.Primes) (w : DeningerPrimeComplexifiedRationalWittPresentation p) :
    deningerPrimeComplexifiedRationalWittFrobenius p w = w ↔
      ∀ g : DeningerPrimeArithmeticGalois p, deningerPrimeComplexifiedRationalWittGaloisAction p g w = w := by
  constructor
  · intro hw g
    obtain ⟨s, v, hv⟩ :=
      deningerPrimeComplexifiedRationalWitt_exists_finiteStage p w
    obtain ⟨n, hn⟩ := deningerPrimeComplexifiedRationalWittGalois_eq_frobeniusPow_on_finiteStage p g s
    calc
      deningerPrimeComplexifiedRationalWittGaloisAction p g w =
          deningerPrimeComplexifiedRationalWittGaloisAction p g
            (deningerPrimeFiniteCyclotomicWittInclusion p s v) :=
        congrArg (deningerPrimeComplexifiedRationalWittGaloisAction p g) hv.symm
      _ = deningerPrimeComplexifiedRationalWittGaloisAction p ((deningerPrimeArithmeticFrobenius p) ^ n)
          (deningerPrimeFiniteCyclotomicWittInclusion p s v) := hn v
      _ = deningerPrimeComplexifiedRationalWittGaloisAction p ((deningerPrimeArithmeticFrobenius p) ^ n) w :=
        congrArg _ hv
      _ = w := deningerPrimeComplexifiedRationalWittGaloisAction_frobeniusPow_fixed p w hw n
  · intro hw
    simpa [deningerPrimeComplexifiedRationalWittGaloisAction_frobenius p] using
      hw (deningerPrimeArithmeticFrobenius p)

end

end RHTower

