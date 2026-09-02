import GaloisForLFunctions.HTGeometry.HahnFractionCorner
import GaloisForLFunctions.HTGeometry.DerivationJetPeel

/-!
# Ramified multigraded Newton derivations

A Puiseux branch becomes integral only after replacing the original coordinate `X_j` by a local
parameter `s_j` with `X_j = s_j ^ (-r_j)`.  The original coordinate derivation is therefore the
Euler derivation divided by `r_j`, shifted by `r_j` degrees.  This module constructs that derivation
on multigraded Hahn series and their fraction field.

The second part proves the discrete lexicographic separation needed by a nested Newton cascade.
If a leading monomial is independent of every coordinate through `j`, then its `j`-derivative
vanishes not merely at the formal shifted boundary: it vanishes below every boundary having the
same zero prefix and `j`-component `r_j`.  This retains the later-coordinate freedom that a genuine
iterated Puiseux expansion requires.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

/-- Degree of the original coordinate `X_j = s_j ^ (-r_j)`. -/
def mgRamUnit {N : ℕ} (r : Fin N → ℕ) (j : Fin N) : mgDeg N :=
  toLex (Pi.single j (-(r j : ℤ)))

/-- Degree shift of differentiation with respect to `X_j`. -/
def mgRamStep {N : ℕ} (r : Fin N → ℕ) (j : Fin N) : mgDeg N :=
  toLex (Pi.single j (r j : ℤ))

@[simp] theorem ofLex_mgRamUnit {N : ℕ} (r : Fin N → ℕ) (j l : Fin N) :
    ofLex (mgRamUnit r j) l = if l = j then -(r j : ℤ) else 0 := by
  rw [mgRamUnit]
  exact Pi.single_apply j (-(r j : ℤ)) l

@[simp] theorem ofLex_mgRamStep {N : ℕ} (r : Fin N → ℕ) (j l : Fin N) :
    ofLex (mgRamStep r j) l = if l = j then (r j : ℤ) else 0 := by
  rw [mgRamStep]
  exact Pi.single_apply j (r j : ℤ) l

/-- Normalized exponent character: `s_j^q` has `X_j`-Euler exponent `q / r_j`. -/
def mgRamComp {N : ℕ} (r : Fin N → ℕ) (j : Fin N) : mgDeg N →+ ℂ where
  toFun γ := ((ofLex γ j : ℤ) : ℂ) / (r j : ℂ)
  map_zero' := by
    have hzero : ofLex (0 : mgDeg N) j = 0 := rfl
    rw [hzero]
    simpa only [Int.cast_zero] using (zero_div (r j : ℂ))
  map_add' a b := by
    change (((ofLex a j + ofLex b j : ℤ) : ℂ) / (r j : ℂ)) = _
    push_cast
    ring

/-- Ramified coordinate-shift monomial. -/
noncomputable def mgRamShift {N : ℕ} (r : Fin N → ℕ) (j : Fin N) :
    HahnSeries (mgDeg N) ℂ :=
  HahnSeries.single (mgRamStep r j) 1

/-- Complex-linear derivative with respect to the original coordinate `X_j`. -/
noncomputable def mgRamPartialComplex {N : ℕ} (r : Fin N → ℕ) (j : Fin N) :
    Derivation ℂ (HahnSeries (mgDeg N) ℂ) (HahnSeries (mgDeg N) ℂ) :=
  (mgRamShift r j) • hahnDerivationComplex (mgRamComp r j)

theorem coeff_mgRamPartialComplex {N : ℕ} (r : Fin N → ℕ) (j : Fin N)
    (f : HahnSeries (mgDeg N) ℂ) (γ : mgDeg N) :
    (mgRamPartialComplex r j f).coeff (γ + mgRamStep r j) =
      (((ofLex γ j : ℤ) : ℂ) / (r j : ℂ)) * f.coeff γ := by
  have hd : mgRamPartialComplex r j f =
      mgRamShift r j * hahnGrade (mgRamComp r j) f := by
    show ((mgRamShift r j) • hahnDerivationComplex (mgRamComp r j)) f = _
    simp only [Derivation.coe_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hd, mgRamShift, HahnSeries.coeff_single_mul, coeff_hahnGrade]
  have hidx : γ + mgRamStep r j - mgRamStep r j = γ := by abel
  rw [hidx]
  change 1 * ((((ofLex γ j : ℤ) : ℂ) / (r j : ℂ)) * f.coeff γ) = _
  ring

/-- Ramified coordinate derivative extended to the Hahn fraction field. -/
noncomputable def hahnFractionRamPartial {N : ℕ} (r : Fin N → ℕ) (j : Fin N) :
    Derivation ℂ (HahnFraction (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) :=
  GaloisForLFunctions.fractionRingDerivation
    ((Algebra.linearMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ)).compDer
      (mgRamPartialComplex r j))

@[simp] theorem hahnFractionRamPartial_algebraMap {N : ℕ} (r : Fin N → ℕ)
    (j : Fin N) (f : HahnSeries (mgDeg N) ℂ) :
    hahnFractionRamPartial r j
        (algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) f) =
      algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ)
        (mgRamPartialComplex r j f) := by
  exact GaloisForLFunctions.fractionRingDerivation_algebraMap
    ((Algebra.linearMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ)).compDer
      (mgRamPartialComplex r j)) f

theorem hasLeadAt_mgRamPartialComplex {N : ℕ} {r : Fin N → ℕ} {j : Fin N}
    {f : HahnSeries (mgDeg N) ℂ} {d : mgDeg N} {c : ℂ}
    (h : HasLeadAt f d c) :
    HasLeadAt (mgRamPartialComplex r j f) (d + mgRamStep r j)
      ((((ofLex d j : ℤ) : ℂ) / (r j : ℂ)) * c) := by
  constructor
  · intro k hk
    have hd : mgRamPartialComplex r j f =
        mgRamShift r j * hahnGrade (mgRamComp r j) f := by
      show ((mgRamShift r j) • hahnDerivationComplex (mgRamComp r j)) f = _
      simp only [Derivation.coe_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [hd, mgRamShift, HahnSeries.coeff_single_mul, coeff_hahnGrade]
    have hlt : k - mgRamStep r j < d := by
      have hstep : k - mgRamStep r j + mgRamStep r j = k := by abel
      refine lt_of_add_lt_add_right (a := mgRamStep r j) ?_
      rw [hstep]
      exact hk
    rw [h.1 _ hlt]
    ring
  · rw [coeff_mgRamPartialComplex, h.2]

/-- A strict lex increase occurring no later than `j` dominates every target whose earlier
coordinates vanish and whose `j`-component is exactly the ramification index. -/
theorem lex_target_lt_add_ramStep_of_le_of_component_ne_zero {N : ℕ}
    {r : Fin N → ℕ} {j : Fin N} {d γ t : mgDeg N}
    (hd : ∀ l, l ≤ j → ofLex d l = 0)
    (ht : ∀ l, l < j → ofLex t l = 0)
    (htj : ofLex t j = (r j : ℤ))
    (hdγ : d ≤ γ) (hγj : ofLex γ j ≠ 0) :
    t < γ + mgRamStep r j := by
  have hdne : d ≠ γ := by
    intro h
    subst γ
    exact hγj (hd j le_rfl)
  have hdlt : d < γ := lt_of_le_of_ne hdγ hdne
  change ∃ p : Fin N,
    (∀ l, l < p → ofLex d l = ofLex γ l) ∧ ofLex d p < ofLex γ p at hdlt
  obtain ⟨p, hpref, hp⟩ := hdlt
  have hpj : p ≤ j := by
    by_contra h
    have hjp : j < p := lt_of_not_ge h
    have heq := hpref j hjp
    exact hγj (heq ▸ hd j le_rfl)
  change ∃ p : Fin N,
    (∀ l, l < p → ofLex t l = ofLex (γ + mgRamStep r j) l) ∧
      ofLex t p < ofLex (γ + mgRamStep r j) p
  refine ⟨p, ?_, ?_⟩
  · intro l hlp
    have hlj : l < j := lt_of_lt_of_le hlp hpj
    have hdl : ofLex d l = 0 := hd l (le_trans (le_of_lt hlp) hpj)
    have hgl : ofLex γ l = 0 := by rw [← hpref l hlp, hdl]
    have hlnj : l ≠ j := ne_of_lt hlj
    change ofLex t l = ofLex γ l + ofLex (mgRamStep r j) l
    rw [ht l hlj, hgl, ofLex_mgRamStep, if_neg hlnj]
    omega
  · rcases lt_or_eq_of_le hpj with hpj' | hpj'
    · have hdp : ofLex d p = 0 := hd p (le_of_lt hpj')
      have htp : ofLex t p = 0 := ht p hpj'
      have hpnj : p ≠ j := ne_of_lt hpj'
      change ofLex t p < ofLex γ p + ofLex (mgRamStep r j) p
      rw [htp, ofLex_mgRamStep, if_neg hpnj]
      rw [hdp] at hp
      omega
    · subst p
      change ofLex t j < ofLex γ j + ofLex (mgRamStep r j) j
      rw [ofLex_mgRamStep, if_pos rfl]
      rw [htj]
      rw [hd j le_rfl] at hp
      omega

/-- Targeted derivative vanishing for a nested lexicographic boundary. -/
theorem HasLeadAt.mgRamPartialComplex_of_prefix_zero {N : ℕ}
    {r : Fin N → ℕ} {j : Fin N} {f : HahnSeries (mgDeg N) ℂ}
    {d t : mgDeg N} {c : ℂ} (hf : HasLeadAt f d c)
    (hd : ∀ l, l ≤ j → ofLex d l = 0)
    (ht : ∀ l, l < j → ofLex t l = 0)
    (htj : ofLex t j = (r j : ℤ)) :
    HasLeadAt (mgRamPartialComplex r j f) t 0 := by
  constructor
  · intro k hkt
    by_contra hk
    let γ := k - mgRamStep r j
    have hidx : γ + mgRamStep r j = k := by
      dsimp [γ]
      abel
    have hcoeff := coeff_mgRamPartialComplex r j f γ
    rw [hidx] at hcoeff
    have hprod : (((ofLex γ j : ℤ) : ℂ) / (r j : ℂ)) * f.coeff γ ≠ 0 := by
      rw [← hcoeff]
      exact hk
    have hfj : f.coeff γ ≠ 0 := (mul_ne_zero_iff.mp hprod).2
    have hγj : ofLex γ j ≠ 0 := by
      intro hz
      apply (mul_ne_zero_iff.mp hprod).1
      rw [hz]
      norm_num
    have hdγ : d ≤ γ := not_lt.mp fun hγd => hfj (hf.1 γ hγd)
    have htk : t < k := by
      rw [← hidx]
      exact lex_target_lt_add_ramStep_of_le_of_component_ne_zero hd ht htj hdγ hγj
    exact (not_lt_of_ge (le_of_lt hkt)) htk
  · by_contra hk
    let γ := t - mgRamStep r j
    have hidx : γ + mgRamStep r j = t := by
      dsimp [γ]
      abel
    have hcoeff := coeff_mgRamPartialComplex r j f γ
    rw [hidx] at hcoeff
    have hprod : (((ofLex γ j : ℤ) : ℂ) / (r j : ℂ)) * f.coeff γ ≠ 0 := by
      rw [← hcoeff]
      exact hk
    have hfj : f.coeff γ ≠ 0 := (mul_ne_zero_iff.mp hprod).2
    have hγj : ofLex γ j ≠ 0 := by
      intro hz
      apply (mul_ne_zero_iff.mp hprod).1
      rw [hz]
      norm_num
    have hdγ : d ≤ γ := not_lt.mp fun hγd => hfj (hf.1 γ hγd)
    have htt :=
      lex_target_lt_add_ramStep_of_le_of_component_ne_zero hd ht htj hdγ hγj
    rw [hidx] at htt
    exact lt_irrefl t htt

/-- A leading fraction can be represented with denominator degree zero. -/
theorem FracHasLeadAt.normalized {N : ℕ} {q : HahnFraction (mgDeg N) ℂ}
    {d : mgDeg N} {c : ℂ} (h : FracHasLeadAt q d c) :
    ∃ (f g : HahnSeries (mgDeg N) ℂ) (a : ℂ),
      HasLeadAt f d (c * a) ∧ HasLeadAt g 0 a ∧ a ≠ 0 ∧
        q = algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) f /
          algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) g := by
  obtain ⟨f, g, e, a, hf, hg, ha, hq⟩ := h
  let m : HahnSeries (mgDeg N) ℂ := HahnSeries.single (-e) 1
  have hm : HasLeadAt m (-e) 1 :=
    (hasCornerAt_single (-e) (1 : ℂ)).toHasLeadAt
  have hmf : HasLeadAt (m * f) d (c * a) := by
    convert hm.mul hf using 1
    · abel
    · ring
  have hmg : HasLeadAt (m * g) 0 a := by
    convert hm.mul hg using 1
    · abel
    · ring
  refine ⟨m * f, m * g, a, hmf, hmg, ha, ?_⟩
  rw [hq]
  have hm0 : algebraMap (HahnSeries (mgDeg N) ℂ)
      (HahnFraction (mgDeg N) ℂ) m ≠ 0 :=
    (map_ne_zero (algebraMap (HahnSeries (mgDeg N) ℂ)
      (HahnFraction (mgDeg N) ℂ))).mpr (hm.ne_zero one_ne_zero)
  simp only [map_mul]
  field_simp

/-- Exact leading coefficient of a ramified coordinate derivative in the fraction field. -/
theorem FracHasLeadAt.hahnFractionRamPartial {N : ℕ} {r : Fin N → ℕ} {j : Fin N}
    {q : HahnFraction (mgDeg N) ℂ} {d : mgDeg N} {c : ℂ}
    (hq : FracHasLeadAt q d c) :
    FracHasLeadAt (hahnFractionRamPartial r j q) (d + mgRamStep r j)
      (((((ofLex d j : ℤ) : ℂ) / (r j : ℂ))) * c) := by
  obtain ⟨f, g, e, a, hf, hg, ha, rfl⟩ := hq
  have hdf := hasLeadAt_mgRamPartialComplex (r := r) (j := j) hf
  have hdg := hasLeadAt_mgRamPartialComplex (r := r) (j := j) hg
  have hleft : HasLeadAt (mgRamPartialComplex r j f * g)
      ((d + mgRamStep r j) + (e + e))
      (((((ofLex (d + e) j : ℤ) : ℂ) / (r j : ℂ)) * (c * a)) * a) := by
    convert hdf.mul hg using 1
    abel
  have hright : HasLeadAt (f * mgRamPartialComplex r j g)
      ((d + mgRamStep r j) + (e + e))
      ((c * a) * ((((ofLex e j : ℤ) : ℂ) / (r j : ℂ)) * a)) := by
    convert hf.mul hdg using 1
    all_goals first | rfl | abel
  have hnum : HasLeadAt
      (mgRamPartialComplex r j f * g - f * mgRamPartialComplex r j g)
      ((d + mgRamStep r j) + (e + e))
      (((((ofLex d j : ℤ) : ℂ) / (r j : ℂ)) * c) * (a * a)) := by
    convert hleft.sub hright using 1
    have hcomp : ((ofLex (d + e) j : ℤ) : ℂ) =
        ((ofLex d j : ℤ) : ℂ) + ((ofLex e j : ℤ) : ℂ) := by
      change (((ofLex d j + ofLex e j : ℤ) : ℂ)) = _
      push_cast
      rfl
    rw [hcomp]
    ring
  refine ⟨mgRamPartialComplex r j f * g - f * mgRamPartialComplex r j g, g * g,
    e + e, a * a, hnum, hg.mul hg, mul_ne_zero ha ha, ?_⟩
  have hg0 : algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) g ≠ 0 :=
    (map_ne_zero (algebraMap (HahnSeries (mgDeg N) ℂ)
      (HahnFraction (mgDeg N) ℂ))).mpr (hg.ne_zero ha)
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul, hahnFractionRamPartial_algebraMap, map_sub, map_mul]
  field_simp

/-- In a zero-prefix coordinate, the fraction derivative vanishes through every compatible
target boundary. -/
theorem FracHasLeadAt.hahnFractionRamPartial_of_prefix_zero {N : ℕ}
    {r : Fin N → ℕ} {j : Fin N} {q : HahnFraction (mgDeg N) ℂ}
    {d t : mgDeg N} {c : ℂ} (hq : FracHasLeadAt q d c)
    (hd : ∀ l, l ≤ j → ofLex d l = 0)
    (ht : ∀ l, l < j → ofLex t l = 0)
    (htj : ofLex t j = (r j : ℤ)) :
    FracHasLeadAt
      (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j q) t 0 := by
  obtain ⟨f, g, a, hf, hg, ha, rfl⟩ := hq.normalized
  have hzero : ∀ l : Fin N, l ≤ j → ofLex (0 : mgDeg N) l = 0 := by
    intro l _
    rfl
  have htd : ∀ l, l < j → ofLex (t - d) l = 0 := by
    intro l hlj
    change ofLex t l - ofLex d l = 0
    rw [ht l hlj, hd l (le_trans (le_of_lt hlj) le_rfl)]
    omega
  have htdj : ofLex (t - d) j = (r j : ℤ) := by
    change ofLex t j - ofLex d j = (r j : ℤ)
    rw [htj, hd j le_rfl]
    omega
  have hdf : HasLeadAt (mgRamPartialComplex r j f) t 0 :=
    hf.mgRamPartialComplex_of_prefix_zero hd ht htj
  have hdg : HasLeadAt (mgRamPartialComplex r j g) (t - d) 0 :=
    hg.mgRamPartialComplex_of_prefix_zero hzero htd htdj
  have hleft : HasLeadAt (mgRamPartialComplex r j f * g) t 0 := by
    convert hdf.mul hg using 1
    · abel
    · ring
  have hright : HasLeadAt (f * mgRamPartialComplex r j g) t 0 := by
    convert hf.mul hdg using 1
    · abel
    · ring
  have hnum : HasLeadAt
      (mgRamPartialComplex r j f * g - f * mgRamPartialComplex r j g) t 0 := by
    simpa using hleft.sub hright
  refine ⟨mgRamPartialComplex r j f * g - f * mgRamPartialComplex r j g, g * g,
    0, a * a, ?_, ?_, mul_ne_zero ha ha, ?_⟩
  · simpa only [add_zero, zero_mul] using hnum
  · simpa only [zero_add] using hg.mul hg
  · have hg0 : algebraMap (HahnSeries (mgDeg N) ℂ)
        (HahnFraction (mgDeg N) ℂ) g ≠ 0 :=
      (map_ne_zero (algebraMap (HahnSeries (mgDeg N) ℂ)
        (HahnFraction (mgDeg N) ℂ))).mpr (hg.ne_zero ha)
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul, hahnFractionRamPartial_algebraMap, map_sub, map_mul]
    field_simp

/-- A fractional leading bound may be weakened to every strictly earlier degree. -/
theorem FracHasLeadAt.mono {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Field R] {q : HahnFraction Γ R} {d e : Γ} {c : R}
    (hq : FracHasLeadAt q e c) (hde : d < e) : FracHasLeadAt q d 0 := by
  obtain ⟨f, g, a, b, hf, hg, hb, hq⟩ := hq
  refine ⟨f, g, a, b, ?_, hg, hb, hq⟩
  have hlt : d + a < e + a := by
    simpa [add_comm] using add_lt_add_right hde a
  convert hf.mono hlt using 1
  ring

/-! ## Ramified suffix degrees and branch products -/

/-- Degree of the suffix product beginning at coordinate `k`. -/
def mgRamSuffixDegree {N : ℕ} (r : Fin N → ℕ) (k : ℕ) : mgDeg N :=
  toLex fun j => if k ≤ (j : ℕ) then -(r j : ℤ) else 0

@[simp] theorem ofLex_mgRamSuffixDegree {N : ℕ} (r : Fin N → ℕ)
    (k : ℕ) (j : Fin N) :
    ofLex (mgRamSuffixDegree r k) j =
      if k ≤ (j : ℕ) then -(r j : ℤ) else 0 := rfl

/-- Expected degree of output (`m=0`) and successive logarithmic states (`m>0`). -/
def mgRamObservableDegree {n : ℕ} (r : Fin (n + 1) → ℕ) (m : Fin (n + 1)) :
    mgDeg (n + 1) :=
  if m = 0 then mgRamUnit r 0 else mgRamSuffixDegree r (m : ℕ)

@[simp] theorem ofLex_mgRamObservableDegree_self {n : ℕ} (r : Fin (n + 1) → ℕ)
    (m : Fin (n + 1)) :
    ofLex (mgRamObservableDegree r m) m = -(r m : ℤ) := by
  by_cases hm : m = 0
  · rw [mgRamObservableDegree, if_pos hm]
    subst m
    exact ofLex_mgRamUnit r 0 0
  · rw [mgRamObservableDegree, if_neg hm, ofLex_mgRamSuffixDegree,
      if_pos le_rfl]

theorem ofLex_mgRamObservableDegree_eq_zero_of_lt {n : ℕ}
    (r : Fin (n + 1) → ℕ) {j m : Fin (n + 1)} (hjm : j < m) :
    ofLex (mgRamObservableDegree r m) j = 0 := by
  have hm : m ≠ 0 := by
    intro hm
    subst m
    exact Fin.not_lt_zero j hjm
  rw [mgRamObservableDegree, if_neg hm, ofLex_mgRamSuffixDegree,
    if_neg (Nat.not_le.mpr (Fin.mk_lt_mk.mp hjm))]

theorem mgRamSuffixDegree_add_step {N : ℕ} (r : Fin N → ℕ) (j : Fin N) :
    mgRamSuffixDegree r (j : ℕ) + mgRamStep r j =
      mgRamSuffixDegree r ((j : ℕ) + 1) := by
  apply ofLex.injective
  funext l
  change ofLex (mgRamSuffixDegree r (j : ℕ)) l + ofLex (mgRamStep r j) l =
    ofLex (mgRamSuffixDegree r ((j : ℕ) + 1)) l
  rw [ofLex_mgRamSuffixDegree, ofLex_mgRamStep, ofLex_mgRamSuffixDegree]
  by_cases hlj : l = j
  · subst l
    simp
  · have hne : (l : ℕ) ≠ (j : ℕ) := by
      exact fun h => hlj (Fin.ext h)
    by_cases hjl : (j : ℕ) < (l : ℕ)
    · have hsucc : (j : ℕ) + 1 ≤ (l : ℕ) := hjl
      rw [if_pos (Nat.le_of_lt hjl), if_neg hlj, if_pos hsucc]
      omega
    · have hnotle : ¬(j : ℕ) ≤ (l : ℕ) := by omega
      have hnotsucc : ¬(j : ℕ) + 1 ≤ (l : ℕ) := by omega
      simp [hnotle, hnotsucc, hlj]

/-- Earlier suffixes are strictly smaller in lexicographic order when ramification indices are
positive. -/
theorem mgRamSuffixDegree_lt {N : ℕ} {r : Fin N → ℕ}
    (hr : ∀ j, 0 < r j) {k l : ℕ} (hkl : k < l) (hkN : k < N) :
    mgRamSuffixDegree r k < mgRamSuffixDegree r l := by
  let p : Fin N := ⟨k, hkN⟩
  change ∃ p : Fin N,
    (∀ j, j < p → ofLex (mgRamSuffixDegree r k) j =
      ofLex (mgRamSuffixDegree r l) j) ∧
      ofLex (mgRamSuffixDegree r k) p < ofLex (mgRamSuffixDegree r l) p
  refine ⟨p, ?_, ?_⟩
  · intro j hjp
    have hjk : (j : ℕ) < k := Fin.mk_lt_mk.mp hjp
    simp [mgRamSuffixDegree, Nat.not_le.mpr hjk,
      Nat.not_le.mpr (lt_trans hjk hkl)]
  · have hp : (p : ℕ) = k := rfl
    have hnot : ¬l ≤ (p : ℕ) := by omega
    change (if k ≤ (p : ℕ) then -(r p : ℤ) else 0) <
      if l ≤ (p : ℕ) then -(r p : ℤ) else 0
    rw [if_pos (by simp [p]), if_neg hnot]
    have hpos : (0 : ℤ) < (r p : ℤ) := by exact_mod_cast hr p
    omega

/-- Product of all branch velocities from coordinate `k` through the last coordinate. -/
def hahnFractionRamSuffixProduct {N : ℕ}
    (A : Fin N → HahnFraction (mgDeg N) ℂ) (k : ℕ) :
    HahnFraction (mgDeg N) ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ (j : ℕ)), A j

/-- Boundary coefficient of a ramified suffix product. -/
def hahnFractionRamSuffixCoefficient {N : ℕ} (lambda : Fin N → ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ (j : ℕ)), lambda j

theorem mgRamSuffixDegree_eq_sum_units {N : ℕ} (r : Fin N → ℕ) (k : ℕ) :
    mgRamSuffixDegree r k =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ (j : ℕ)), mgRamUnit r j := by
  apply ofLex.injective
  funext l
  change ofLex (mgRamSuffixDegree r k) l =
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => k ≤ (j : ℕ)),
      ofLex (mgRamUnit r j)) l
  simp only [Finset.sum_apply]
  rw [ofLex_mgRamSuffixDegree]
  simp_rw [ofLex_mgRamUnit]
  by_cases hkl : k ≤ (l : ℕ)
  · rw [if_pos hkl]
    simp [hkl]
  · rw [if_neg hkl]
    simp [hkl]

theorem hahnFractionRamSuffixProduct_hasLeadAt {N : ℕ}
    {r : Fin N → ℕ} (A : Fin N → HahnFraction (mgDeg N) ℂ)
    (lambda : Fin N → ℂ)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamUnit r j) (lambda j)) (k : ℕ) :
    FracHasLeadAt (hahnFractionRamSuffixProduct A k) (mgRamSuffixDegree r k)
      (hahnFractionRamSuffixCoefficient lambda k) := by
  rw [hahnFractionRamSuffixCoefficient]
  rw [mgRamSuffixDegree_eq_sum_units]
  exact FracHasLeadAt.prod A (mgRamUnit r) lambda
    (Finset.univ.filter (fun j : Fin N => k ≤ (j : ℕ)))
    (fun j _ => hA j)

theorem mgRamUnit_add_step {N : ℕ} (r : Fin N → ℕ) (j : Fin N) :
    mgRamUnit r j + mgRamStep r j = 0 := by
  apply ofLex.injective
  funext l
  change ofLex (mgRamUnit r j) l + ofLex (mgRamStep r j) l = 0
  rw [ofLex_mgRamUnit, ofLex_mgRamStep]
  by_cases hlj : l = j <;> simp [hlj]

theorem mgRamSuffixDegree_zero_eq {n : ℕ} (r : Fin (n + 1) → ℕ) :
    mgRamSuffixDegree r 0 = mgRamUnit r 0 + mgRamSuffixDegree r 1 := by
  apply ofLex.injective
  funext l
  change ofLex (mgRamSuffixDegree r 0) l =
    ofLex (mgRamUnit r 0) l + ofLex (mgRamSuffixDegree r 1) l
  rw [ofLex_mgRamSuffixDegree, ofLex_mgRamUnit, ofLex_mgRamSuffixDegree]
  by_cases hl0 : l = 0
  · subst l
    simp
  · have hpos : 1 ≤ (l : ℕ) := by
      have : (l : ℕ) ≠ 0 := fun h => hl0 (Fin.ext h)
      omega
    simp [hl0, hpos]

theorem mgRam_main_degree {n : ℕ} (r : Fin (n + 1) → ℕ)
    (m : Fin (n + 1)) :
    mgRamSuffixDegree r (m : ℕ) +
        (mgRamObservableDegree r m + mgRamStep r m) =
      mgRamObservableDegree r m + mgRamSuffixDegree r ((m : ℕ) + 1) := by
  by_cases hm : m = 0
  · subst m
    rw [mgRamObservableDegree, if_pos rfl, mgRamUnit_add_step, add_zero]
    simpa using mgRamSuffixDegree_zero_eq r
  · rw [mgRamObservableDegree, if_neg hm, mgRamSuffixDegree_add_step]

theorem mgRam_higher_term_degree {n : ℕ} (r : Fin (n + 1) → ℕ)
    (m j : Fin (n + 1)) :
    mgRamSuffixDegree r (j : ℕ) +
        (mgRamObservableDegree r m + mgRamStep r j) =
      mgRamObservableDegree r m + mgRamSuffixDegree r ((j : ℕ) + 1) := by
  rw [← mgRamSuffixDegree_add_step r j]
  abel

theorem mgRam_lower_derivative_target_prefix {n : ℕ}
    (r : Fin (n + 1) → ℕ) {j m : Fin (n + 1)} (hjm : j < m) :
    let t := mgRamObservableDegree r m + mgRamSuffixDegree r ((m : ℕ) + 1) -
      mgRamSuffixDegree r (j : ℕ)
    (∀ l, l < j → ofLex t l = 0) ∧ ofLex t j = (r j : ℤ) := by
  dsimp only
  constructor
  · intro l hlj
    have hlm : l < m := lt_trans hlj hjm
    change ofLex (mgRamObservableDegree r m) l +
        ofLex (mgRamSuffixDegree r ((m : ℕ) + 1)) l -
        ofLex (mgRamSuffixDegree r (j : ℕ)) l = 0
    rw [ofLex_mgRamObservableDegree_eq_zero_of_lt r hlm,
      ofLex_mgRamSuffixDegree, ofLex_mgRamSuffixDegree]
    have hnotm : ¬(m : ℕ) + 1 ≤ (l : ℕ) := by omega
    have hnotj : ¬(j : ℕ) ≤ (l : ℕ) := by exact Nat.not_le.mpr (Fin.mk_lt_mk.mp hlj)
    rw [if_neg hnotm, if_neg hnotj]
    omega
  · change ofLex (mgRamObservableDegree r m) j +
        ofLex (mgRamSuffixDegree r ((m : ℕ) + 1)) j -
        ofLex (mgRamSuffixDegree r (j : ℕ)) j = (r j : ℤ)
    rw [ofLex_mgRamObservableDegree_eq_zero_of_lt r hjm,
      ofLex_mgRamSuffixDegree, ofLex_mgRamSuffixDegree]
    have hnotm : ¬(m : ℕ) + 1 ≤ (j : ℕ) := by omega
    rw [if_neg hnotm, if_pos le_rfl]
    omega

/-! ## Ramified product-cascade derivation -/

/-- Cascade vector field in reversed coordinates: coordinate zero is terminal output and
`δ X_j` is the suffix product beginning at `j`. -/
noncomputable def hahnFractionRamCascadeDerivation {N : ℕ} (r : Fin N → ℕ)
    (A : Fin N → HahnFraction (mgDeg N) ℂ) :
    Derivation ℂ (HahnFraction (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) :=
  ∑ j : Fin N, (-hahnFractionRamSuffixProduct A (j : ℕ)) •
    GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j

@[simp] theorem hahnFractionRamCascadeDerivation_apply {N : ℕ} (r : Fin N → ℕ)
    (A : Fin N → HahnFraction (mgDeg N) ℂ) (y : HahnFraction (mgDeg N) ℂ) :
    hahnFractionRamCascadeDerivation r A y =
      ∑ j : Fin N, (-hahnFractionRamSuffixProduct A (j : ℕ)) *
        GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j y := by
  classical
  rw [hahnFractionRamCascadeDerivation]
  let s : Finset (Fin N) := Finset.univ
  change (∑ j ∈ s, (-hahnFractionRamSuffixProduct A (j : ℕ)) •
      GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j) y =
    ∑ j ∈ s, (-hahnFractionRamSuffixProduct A (j : ℕ)) *
      GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j y
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change (-hahnFractionRamSuffixProduct A (a : ℕ)) *
          GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r a y +
          (∑ j ∈ s, (-hahnFractionRamSuffixProduct A (j : ℕ)) •
            GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j) y = _
      rw [ih]

/-- **Ramified nested-cascade transition.** A state with the expected output/logarithmic-state
boundary has, after one logarithmic derivative along the product-cascade vector field, exactly the
next suffix-product boundary. No restriction is placed on later Puiseux exponents. -/
theorem hahnFractionRamCascade_logarithmicStep_hasLeadAt {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (lambda : Fin (n + 1) → ℂ)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamUnit r j) (lambda j))
    (m : Fin (n + 1)) (y : HahnFraction (mgDeg (n + 1)) ℂ) (c : ℂ)
    (hc : c ≠ 0)
    (hy : FracHasLeadAt y (mgRamObservableDegree r m) c) :
    FracHasLeadAt (hahnFractionRamCascadeDerivation r A y / y)
      (mgRamSuffixDegree r ((m : ℕ) + 1))
      (hahnFractionRamSuffixCoefficient lambda (m : ℕ)) := by
  classical
  let E := mgRamObservableDegree r m
  let U := fun k : ℕ => mgRamSuffixDegree r k
  let Q := fun j : Fin (n + 1) => hahnFractionRamSuffixProduct A (j : ℕ)
  let q := fun j : Fin (n + 1) => hahnFractionRamSuffixCoefficient lambda (j : ℕ)
  let T := E + U ((m : ℕ) + 1)
  have hQ : ∀ j, FracHasLeadAt (Q j) (U (j : ℕ)) (q j) := by
    intro j
    exact hahnFractionRamSuffixProduct_hasLeadAt A lambda hA (j : ℕ)
  have hterm : ∀ j : Fin (n + 1),
      FracHasLeadAt ((-Q j) *
        GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j y) T
        (if j = m then q m * c else 0) := by
    intro j
    by_cases hjm : j = m
    · subst j
      have hrC : (r m : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (hr m))
      have hdy : FracHasLeadAt
          (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r m y)
          (E + mgRamStep r m) (-c) := by
        have h := hy.hahnFractionRamPartial (r := r) (j := m)
        change FracHasLeadAt
          (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r m y)
          (E + mgRamStep r m) (-c)
        convert h using 1
        rw [ofLex_mgRamObservableDegree_self]
        push_cast
        field_simp
      have hmain := (hQ m).neg.mul hdy
      rw [if_pos rfl]
      convert hmain using 1
      · dsimp [T, E, U]
        exact (mgRam_main_degree r m).symm
      · ring
    · rcases lt_or_gt_of_ne hjm with hjm' | hmj
      · have hd : ∀ l, l ≤ j → ofLex E l = 0 := by
          intro l hlj
          exact ofLex_mgRamObservableDegree_eq_zero_of_lt r (lt_of_le_of_lt hlj hjm')
        let t := E + U ((m : ℕ) + 1) - U (j : ℕ)
        have htdata := mgRam_lower_derivative_target_prefix r hjm'
        change (∀ l, l < j → ofLex t l = 0) ∧ ofLex t j = (r j : ℤ) at htdata
        have hdy : FracHasLeadAt
            (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j y) t 0 :=
          hy.hahnFractionRamPartial_of_prefix_zero hd htdata.1 htdata.2
        have hzero := (hQ j).neg.mul hdy
        rw [if_neg hjm]
        convert hzero using 1
        · dsimp [t, T]
          abel
        · ring
      · have hdy := hy.hahnFractionRamPartial (r := r) (j := j)
        have hhigh := (hQ j).neg.mul hdy
        have hmjNat : (m : ℕ) + 1 < (j : ℕ) + 1 := by omega
        have hmN : (m : ℕ) + 1 < n + 1 := by
          have hjN : (j : ℕ) < n + 1 := j.isLt
          omega
        have hsuffix : U ((m : ℕ) + 1) < U ((j : ℕ) + 1) :=
          mgRamSuffixDegree_lt hr hmjNat hmN
        have hdegree : T < E + U ((j : ℕ) + 1) := by
          dsimp [T]
          simpa [add_comm] using add_lt_add_left hsuffix E
        have hhigh' : FracHasLeadAt ((-Q j) *
            GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j y)
            (E + U ((j : ℕ) + 1))
            ((-q j) *
              (((((ofLex E j : ℤ) : ℂ) / (r j : ℂ))) * c)) := by
          convert hhigh using 1
          dsimp [E, U]
          exact (mgRam_higher_term_degree r m j).symm
        rw [if_neg hjm]
        exact hhigh'.mono hdegree
  have hsum : FracHasLeadAt
      (∑ j : Fin (n + 1), (-Q j) *
        GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j y)
      T (q m * c) := by
    have h := FracHasLeadAt.sum
      (fun j : Fin (n + 1) => (-Q j) *
        GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j y)
      T (fun j => if j = m then q m * c else 0) Finset.univ
      (fun j _ => hterm j)
    simpa using h
  have hdelta : FracHasLeadAt (hahnFractionRamCascadeDerivation r A y)
      T (q m * c) := by
    rw [hahnFractionRamCascadeDerivation_apply]
    exact hsum
  have hquot := hdelta.div hy hc
  convert hquot using 1
  · dsimp [T, E, U]
    abel
  · dsimp [q]
    field_simp

/-- Original coordinate `X_j = s_j^(-r_j)` inside the multigraded Hahn fraction field. -/
noncomputable def hahnFractionRamCoordinate {N : ℕ} (r : Fin N → ℕ) (j : Fin N) :
    HahnFraction (mgDeg N) ℂ :=
  algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ)
    (HahnSeries.single (mgRamUnit r j) 1)

theorem hahnFractionRamCoordinate_hasLeadAt {N : ℕ} (r : Fin N → ℕ) (j : Fin N) :
    FracHasLeadAt (hahnFractionRamCoordinate r j) (mgRamUnit r j) 1 := by
  exact FracHasLeadAt.of_hahn
    (hasCornerAt_single (mgRamUnit r j) (1 : ℂ)).toHasLeadAt

theorem hahnFractionRamSuffixCoefficient_ne_zero {N : ℕ} {lambda : Fin N → ℂ}
    (hlambda : ∀ j, lambda j ≠ 0) (k : ℕ) :
    hahnFractionRamSuffixCoefficient lambda k ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun j _ => hlambda j

/-- Terminal coordinate followed by its iterated logarithmic derivatives along the ramified
product-cascade vector field. -/
noncomputable def hahnFractionRamLogState {n : ℕ}
    (r : Fin (n + 1) → ℕ)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ) :
    ℕ → HahnFraction (mgDeg (n + 1)) ℂ
  | 0 => hahnFractionRamCoordinate r 0
  | k + 1 =>
      hahnFractionRamCascadeDerivation r A (hahnFractionRamLogState r A k) /
        hahnFractionRamLogState r A k

@[simp] theorem hahnFractionRamLogState_zero {n : ℕ}
    (r : Fin (n + 1) → ℕ)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ) :
    hahnFractionRamLogState r A 0 = hahnFractionRamCoordinate r 0 := rfl

@[simp] theorem hahnFractionRamLogState_succ {n : ℕ}
    (r : Fin (n + 1) → ℕ)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ) (k : ℕ) :
    hahnFractionRamLogState r A (k + 1) =
      hahnFractionRamCascadeDerivation r A (hahnFractionRamLogState r A k) /
        hahnFractionRamLogState r A k := rfl

/-- Every observable in the ramified logarithmic chain has its exact nested suffix boundary. -/
theorem hahnFractionRamLogState_exists_lead {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (lambda : Fin (n + 1) → ℂ) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamUnit r j) (lambda j))
    (m : Fin (n + 1)) :
    ∃ c : ℂ, c ≠ 0 ∧
      FracHasLeadAt (hahnFractionRamLogState r A (m : ℕ))
        (mgRamObservableDegree r m) c := by
  have hnat : ∀ k : ℕ, (hk : k < n + 1) →
      ∃ c : ℂ, c ≠ 0 ∧
        FracHasLeadAt (hahnFractionRamLogState r A k)
          (mgRamObservableDegree r ⟨k, hk⟩) c := by
    intro k
    induction k with
    | zero =>
        intro hk
        refine ⟨1, one_ne_zero, ?_⟩
        have hfin : (⟨0, hk⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
        rw [mgRamObservableDegree, if_pos hfin]
        exact hahnFractionRamCoordinate_hasLeadAt r 0
    | succ k ih =>
        intro hk
        have hk' : k < n + 1 := by omega
        obtain ⟨c, hc, hstate⟩ := ih hk'
        let km : Fin (n + 1) := ⟨k, hk'⟩
        have hnext := hahnFractionRamCascade_logarithmicStep_hasLeadAt
          r hr A lambda hA km (hahnFractionRamLogState r A k) c hc hstate
        refine ⟨hahnFractionRamSuffixCoefficient lambda k,
          hahnFractionRamSuffixCoefficient_ne_zero hlambda k, ?_⟩
        rw [hahnFractionRamLogState_succ]
        have hne : (⟨k + 1, hk⟩ : Fin (n + 1)) ≠ 0 := by
          intro h
          have := Fin.ext_iff.mp h
          simp at this
        rw [mgRamObservableDegree, if_neg hne]
        exact hnext
  exact hnat (m : ℕ) m.isLt

/-! ## Ramified gradient determinant and observability -/

/-- Coordinate-gradient matrix for ramified original-coordinate derivations. -/
def hahnFractionRamGradientMatrix {N : ℕ} (r : Fin N → ℕ)
    (f : Fin N → HahnFraction (mgDeg N) ℂ) :
    Matrix (Fin N) (Fin N) (HahnFraction (mgDeg N) ℂ) :=
  fun i j => GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j (f i)

theorem mgRamObservable_derivativeCoefficient {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (c : Fin (n + 1) → ℂ) (i j : Fin (n + 1)) :
    (((ofLex (mgRamObservableDegree r i) j : ℤ) : ℂ) / (r j : ℂ)) * c i =
      hahnFractionNestedCascadeLeadMatrix c i j := by
  have hrC : (r j : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hr j))
  by_cases hi : i = 0
  · subst i
    rw [mgRamObservableDegree, if_pos rfl]
    by_cases hj : j = 0
    · subst j
      rw [ofLex_mgRamUnit]
      simp only [hahnFractionNestedCascadeLeadMatrix]
      push_cast
      field_simp
    · rw [ofLex_mgRamUnit, if_neg hj]
      simp [hahnFractionNestedCascadeLeadMatrix, hj]
  · rw [mgRamObservableDegree, if_neg hi, ofLex_mgRamSuffixDegree]
    by_cases hij : (i : ℕ) ≤ (j : ℕ)
    · rw [if_pos hij]
      simp only [hahnFractionNestedCascadeLeadMatrix, if_neg hi, if_pos hij]
      push_cast
      field_simp
    · rw [if_neg hij]
      simp [hahnFractionNestedCascadeLeadMatrix, hi, hij]

theorem hahnFractionRamGradientMatrix_det_ne_zero_of_nestedCascade_leads {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (f : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (c : Fin (n + 1) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hf : ∀ i, FracHasLeadAt (f i) (mgRamObservableDegree r i) (c i)) :
    (hahnFractionRamGradientMatrix r f).det ≠ 0 := by
  refine fracDet_ne_zero_of_hasLeadAt (hahnFractionRamGradientMatrix r f)
    (mgRamObservableDegree r) (mgRamStep r)
    (hahnFractionNestedCascadeLeadMatrix c) ?_
    (hahnFractionNestedCascadeLeadMatrix_det_ne_zero c hc)
  intro i j
  have h := (hf i).hahnFractionRamPartial (r := r) (j := j)
  change FracHasLeadAt
    (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j (f i))
    (mgRamObservableDegree r i + mgRamStep r j)
    (hahnFractionNestedCascadeLeadMatrix c i j)
  convert h using 1
  exact (mgRamObservable_derivativeCoefficient r hr c i j).symm

theorem algebraicIndependent_of_hahnFractionRamGradientMatrix_det_ne_zero {N : ℕ}
    (r : Fin N → ℕ) (f : Fin N → HahnFraction (mgDeg N) ℂ)
    (hdet : (hahnFractionRamGradientMatrix r f).det ≠ 0) :
    AlgebraicIndependent ℂ f := by
  let M : Matrix (Fin N) (Fin N) (HahnFraction (mgDeg N) ℂ) :=
    Matrix.transpose (hahnFractionRamGradientMatrix r f)
  have hM : M.det ≠ 0 := by
    simpa [M, Matrix.det_transpose] using hdet
  refine algebraicIndependent_of_domain_jacobian f
    (fun i => GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r i) ?_ ?_ ?_ M hM ?_
  · intro i a b
    exact map_add (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r i) a b
  · intro i a b
    simpa only [smul_eq_mul, add_comm, mul_comm] using
      (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r i).leibniz a b
  · intro i z
    exact (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r i).map_algebraMap z
  · intro i j
    rfl

/-- **Exact ramified Puiseux observability for algebraic product cascades.** Any collection of
nonzero output-linear Puiseux branch leads forces algebraic independence of terminal output and
all logarithmic states. Higher branch terms are unrestricted. -/
theorem algebraicIndependent_hahnFractionRamLogState {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (lambda : Fin (n + 1) → ℂ) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamUnit r j) (lambda j)) :
    AlgebraicIndependent ℂ
      (fun i : Fin (n + 1) => hahnFractionRamLogState r A (i : ℕ)) := by
  choose c hc hf using fun i =>
    hahnFractionRamLogState_exists_lead r hr A lambda hlambda hA i
  apply algebraicIndependent_of_hahnFractionRamGradientMatrix_det_ne_zero r
  exact hahnFractionRamGradientMatrix_det_ne_zero_of_nestedCascade_leads r hr _ c hc hf

/-! ## Finite logarithmic peel and output jets -/

/-- Bounded form of the chain peel: only the `N` logarithmic states used by the determinant need
to satisfy the recursion. -/
theorem peelMatrix_det_chain_of_lt
    {R : Type*} [CommRing R] [Algebra ℂ R] {N : ℕ}
    (delta : Derivation ℂ R R) (D : Fin N → Derivation ℂ R R)
    (Y : ℕ → R) (hchain : ∀ m, m < N → delta (Y m) = Y (m + 1) * Y m) :
    ∀ (d k : ℕ), k + d = N →
      (peelMatrix delta D (fun m j => D j (Y m)) k (Y k)).det =
        (∏ m ∈ Finset.Ico k N, Y m ^ (N - (m + 1))) * (gradientMatrix D Y).det := by
  classical
  intro d
  induction d with
  | zero =>
      intro k hkd
      have hk : k = N := by omega
      subst hk
      rw [peelMatrix_full, Finset.Ico_self, Finset.prod_empty, one_mul]
  | succ d ih =>
      intro k hkd
      have hk : k < N := by omega
      rw [peelMatrix_det_succ hk delta D (fun m j => D j (Y m))
        (Y k) (Y (k + 1)) (hchain k hk)]
      have hupd : Function.update (fun m j => D j (Y m)) k (fun j => D j (Y k)) =
          fun m j => D j (Y m) :=
        Function.update_eq_self (β := fun _ => Fin N → R) k (fun m j => D j (Y m))
      rw [hupd, ih (k + 1) (by omega),
        Finset.prod_eq_prod_Ico_succ_bot hk (fun m => Y m ^ (N - (m + 1))), mul_assoc]

theorem outputJacobian_det_eq_gradientMatrix_of_lt
    {R : Type*} [CommRing R] [Algebra ℂ R] {N : ℕ}
    (delta : Derivation ℂ R R) (D : Fin N → Derivation ℂ R R)
    (Y : ℕ → R) (hchain : ∀ m, m < N → delta (Y m) = Y (m + 1) * Y m) :
    (Matrix.of fun (i : Fin N) (j : Fin N) =>
        D j (((delta : R → R)^[(i : ℕ)]) (Y 0))).det =
      (∏ m ∈ Finset.range N, Y m ^ (N - (m + 1))) * (gradientMatrix D Y).det := by
  have h := peelMatrix_det_chain_of_lt delta D Y hchain N 0 (by omega)
  have hmat : peelMatrix delta D (fun m j => D j (Y m)) 0 (Y 0) =
      Matrix.of fun (i : Fin N) (j : Fin N) =>
        D j (((delta : R → R)^[(i : ℕ)]) (Y 0)) := by
    funext i j
    exact peelMatrix_zero_apply delta D (fun m j => D j (Y m)) (Y 0) i j
  rw [hmat] at h
  rw [h, Finset.range_eq_Ico]

theorem outputJacobian_det_ne_zero_of_gradientMatrix_of_lt
    {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R] {N : ℕ}
    (delta : Derivation ℂ R R) (D : Fin N → Derivation ℂ R R)
    (Y : ℕ → R) (hchain : ∀ m, m < N → delta (Y m) = Y (m + 1) * Y m)
    (hne : ∀ m, m < N → Y m ≠ 0) (hgrad : (gradientMatrix D Y).det ≠ 0) :
    (Matrix.of fun (i : Fin N) (j : Fin N) =>
      D j (((delta : R → R)^[(i : ℕ)]) (Y 0))).det ≠ 0 := by
  rw [outputJacobian_det_eq_gradientMatrix_of_lt delta D Y hchain]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun m hm =>
      pow_ne_zero _ (hne m (Finset.mem_range.mp hm))) hgrad

/-- The first `N` time jets are independent whenever their coordinate-observability determinant is
nonzero. -/
theorem algebraicIndependent_of_hahnFractionRamOutputJacobian_det_ne_zero {N : ℕ}
    (r : Fin N → ℕ) (delta : Derivation ℂ (HahnFraction (mgDeg N) ℂ)
      (HahnFraction (mgDeg N) ℂ)) (x : HahnFraction (mgDeg N) ℂ)
    (hdet : (Matrix.of fun (i : Fin N) (j : Fin N) =>
      GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j
        (((delta : HahnFraction (mgDeg N) ℂ → HahnFraction (mgDeg N) ℂ)^[(i : ℕ)]) x)).det ≠ 0) :
    AlgebraicIndependent ℂ (fun i : Fin N =>
      ((delta : HahnFraction (mgDeg N) ℂ → HahnFraction (mgDeg N) ℂ)^[(i : ℕ)]) x) := by
  let f := fun i : Fin N =>
    ((delta : HahnFraction (mgDeg N) ℂ → HahnFraction (mgDeg N) ℂ)^[(i : ℕ)]) x
  let M : Matrix (Fin N) (Fin N) (HahnFraction (mgDeg N) ℂ) :=
    Matrix.transpose (Matrix.of fun (i : Fin N) (j : Fin N) =>
      GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j (f i))
  have hM : M.det ≠ 0 := by
    simpa [M, f, Matrix.det_transpose] using hdet
  refine algebraicIndependent_of_domain_jacobian f
    (fun i => GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r i) ?_ ?_ ?_ M hM ?_
  · intro i a b
    exact map_add (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r i) a b
  · intro i a b
    simpa only [smul_eq_mul, add_comm, mul_comm] using
      (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r i).leibniz a b
  · intro i z
    exact (GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r i).map_algebraMap z
  · intro i j
    rfl

/-- The ramified product-cascade output-jet observability determinant is nonzero. -/
theorem hahnFractionRamCascade_outputJacobian_det_ne_zero {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (lambda : Fin (n + 1) → ℂ) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamUnit r j) (lambda j)) :
    (Matrix.of fun (i : Fin (n + 1)) (j : Fin (n + 1)) =>
      GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j
        ((((hahnFractionRamCascadeDerivation r A :
          HahnFraction (mgDeg (n + 1)) ℂ → HahnFraction (mgDeg (n + 1)) ℂ)^[(i : ℕ)]))
          (hahnFractionRamCoordinate r 0))).det ≠ 0 := by
  let Y := hahnFractionRamLogState r A
  let delta := hahnFractionRamCascadeDerivation r A
  let P := fun j : Fin (n + 1) =>
    GaloisForLFunctions.HTGeometry.hahnFractionRamPartial r j
  choose c hc hY using fun i =>
    hahnFractionRamLogState_exists_lead r hr A lambda hlambda hA i
  have hne : ∀ m, m < n + 1 → Y m ≠ 0 := by
    intro m hm
    exact (hY ⟨m, hm⟩).ne_zero (hc ⟨m, hm⟩)
  have hchain : ∀ m, m < n + 1 → delta (Y m) = Y (m + 1) * Y m := by
    intro m hm
    dsimp only [delta, Y]
    rw [hahnFractionRamLogState_succ]
    exact (div_mul_cancel₀
      (hahnFractionRamCascadeDerivation r A (hahnFractionRamLogState r A m))
      (hne m hm)).symm
  have hgrad : (gradientMatrix P Y).det ≠ 0 := by
    have hdet := hahnFractionRamGradientMatrix_det_ne_zero_of_nestedCascade_leads
      r hr (fun i : Fin (n + 1) => Y (i : ℕ)) c hc hY
    exact hdet
  have hdet := outputJacobian_det_ne_zero_of_gradientMatrix_of_lt
    delta P Y hchain hne hgrad
  exact hdet

/-- **Ramified product-cascade output-jet observability.** The first `n+1` time derivatives of the
terminal coordinate are algebraically independent for every collection of nonzero output-linear
Puiseux branch leads, with arbitrary higher terms. -/
theorem algebraicIndependent_hahnFractionRamCascadeOutputJets {n : ℕ}
    (r : Fin (n + 1) → ℕ) (hr : ∀ j, 0 < r j)
    (A : Fin (n + 1) → HahnFraction (mgDeg (n + 1)) ℂ)
    (lambda : Fin (n + 1) → ℂ) (hlambda : ∀ j, lambda j ≠ 0)
    (hA : ∀ j, FracHasLeadAt (A j) (mgRamUnit r j) (lambda j)) :
    AlgebraicIndependent ℂ (fun i : Fin (n + 1) =>
      (((hahnFractionRamCascadeDerivation r A :
        HahnFraction (mgDeg (n + 1)) ℂ → HahnFraction (mgDeg (n + 1)) ℂ)^[(i : ℕ)])
        (hahnFractionRamCoordinate r 0))) := by
  have hdet := hahnFractionRamCascade_outputJacobian_det_ne_zero
    r hr A lambda hlambda hA
  exact algebraicIndependent_of_hahnFractionRamOutputJacobian_det_ne_zero r
    (hahnFractionRamCascadeDerivation r A) (hahnFractionRamCoordinate r 0) hdet

end GaloisForLFunctions.HTGeometry
