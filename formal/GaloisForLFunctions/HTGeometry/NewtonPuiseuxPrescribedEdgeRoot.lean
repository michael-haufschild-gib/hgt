import GaloisForLFunctions.HTGeometry.NewtonPuiseuxFiniteFamily
import GaloisForLFunctions.HTGeometry.NewtonSlopeTransform

/-!
# Newton--Puiseux lifting with a prescribed edge root

An arbitrary Newton--Puiseux root does not remember which root of the Newton-edge polynomial was
chosen.  This file retains that information.  The full root-multiplicity factor of the special
fibre is first lifted together with its exact reduction.  Newton--Puiseux applied to that factor
then produces a ramified root whose constant coefficient is the prescribed edge root.  Substitution
back through the Newton transform gives a root of the original polynomial with that exact leading
coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {K : Type} [Field K]

/-- A root-multiplicity factor lifts from any nonzero special fibre.  The ambient polynomial need
not be monic: Hensel factorization only requires the selected fibre factor itself to be monic. -/
theorem exists_monic_factor_of_rootMultiplicity_with_reduction_of_specialFiber_ne
    {f : (PowerSeries K)[X]}
    (hfne : f.map (PowerSeries.constantCoeff (R := K)) ≠ 0) (c : K) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧
      g.natDegree = (f.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity c ∧
      f = g * h ∧
      g.map (PowerSeries.constantCoeff (R := K)) =
        ((X : K[X]) - Polynomial.C c) ^
          (f.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity c := by
  classical
  set F : K[X] := f.map (PowerSeries.constantCoeff (R := K)) with hFdef
  set m : ℕ := F.rootMultiplicity c with hmdef
  set q : K[X] := ((X : K[X]) - Polynomial.C c) ^ m with hqdef
  have hqmonic : q.Monic := (monic_X_sub_C c).pow m
  set b : K[X] := F /ₘ q with hbdef
  have hFfact : F = q * b := by
    have hzero : F %ₘ q = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hqmonic).mpr (pow_rootMultiplicity_dvd F c)
    have hadd := Polynomial.modByMonic_add_div F q
    rw [hzero, zero_add] at hadd
    exact hadd.symm
  have heval : b.eval c ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c (hFdef ▸ hfne)
  have hnotdvd : ¬ (((X : K[X]) - Polynomial.C c) ∣ b) := by
    rw [Polynomial.dvd_iff_isRoot]
    exact heval
  have hcop : IsCoprime ((X : K[X]) - Polynomial.C c) b := by
    by_contra hc
    exact hnotdvd ((Polynomial.irreducible_X_sub_C c).dvd_iff_not_isCoprime.mpr hc)
  obtain ⟨g, h, hgm, hgdeg, hfgh, hgred, _⟩ :=
    exists_factorization_of_coprime_reduction (a := q) (b := b) hqmonic hFfact hcop.pow_left
  have hqdegree : q.natDegree = m := by
    rw [hqdef, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  refine ⟨g, h, hgm, ?_, hfgh, ?_⟩
  · rw [Polynomial.natDegree_eq_of_degree_eq hgdeg, hqdegree]
  · simpa [hFdef, hmdef, hqdef] using hgred

/-- A root-multiplicity factor can be lifted while retaining its exact special fibre. -/
theorem exists_monic_factor_of_rootMultiplicity_with_reduction
    {f : (PowerSeries K)[X]} (hf : f.Monic) (c : K) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧ h.Monic ∧
      g.natDegree = (f.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity c ∧
      f = g * h ∧
      g.map (PowerSeries.constantCoeff (R := K)) =
        ((X : K[X]) - Polynomial.C c) ^
          (f.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity c := by
  classical
  set F : K[X] := f.map (PowerSeries.constantCoeff (R := K)) with hFdef
  have hFmonic : F.Monic := hf.map _
  have hFne : F ≠ 0 := hFmonic.ne_zero
  set m : ℕ := F.rootMultiplicity c with hmdef
  set q : K[X] := ((X : K[X]) - Polynomial.C c) ^ m with hqdef
  have hqmonic : q.Monic := (monic_X_sub_C c).pow m
  set b : K[X] := F /ₘ q with hbdef
  have hFfact : F = q * b := by
    have hzero : F %ₘ q = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hqmonic).mpr (pow_rootMultiplicity_dvd F c)
    have hadd := Polynomial.modByMonic_add_div F q
    rw [hzero, zero_add] at hadd
    exact hadd.symm
  have heval : b.eval c ≠ 0 :=
    Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero c hFne
  have hnotdvd : ¬ (((X : K[X]) - Polynomial.C c) ∣ b) := by
    rw [Polynomial.dvd_iff_isRoot]
    exact heval
  have hcop : IsCoprime ((X : K[X]) - Polynomial.C c) b := by
    by_contra hc
    exact hnotdvd ((Polynomial.irreducible_X_sub_C c).dvd_iff_not_isCoprime.mpr hc)
  obtain ⟨g, h, hgm, hgdeg, hfgh, hgred, _⟩ :=
    exists_factorization_of_coprime_reduction (a := q) (b := b) hqmonic hFfact hcop.pow_left
  have hqdegree : q.natDegree = m := by
    rw [hqdef, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  refine ⟨g, h, hgm, hgm.of_mul_monic_left (hfgh ▸ hf), ?_, hfgh, ?_⟩
  · rw [Polynomial.natDegree_eq_of_degree_eq hgdeg, hqdegree]
  · simpa [hFdef, hmdef, hqdef] using hgred

/-- A ramified root of a factor reducing to a pure root-multiplicity power has the prescribed
constant coefficient. -/
theorem constantCoeff_eq_of_isRoot_map_expand_rootMultiplicity_factor
    {g : (PowerSeries K)[X]} {c : K} {m N : ℕ} (hN : N ≠ 0)
    (hgred : g.map (PowerSeries.constantCoeff (R := K)) =
      ((X : K[X]) - Polynomial.C c) ^ m)
    {y : PowerSeries K}
    (hy : (g.map (PowerSeries.expand (R := K) N hN).toRingHom).IsRoot y) :
    PowerSeries.constantCoeff y = c := by
  have hyc := isRoot_map_powerSeries (PowerSeries.constantCoeff (R := K)) hy
  rw [Polynomial.map_map] at hyc
  have hcomp :
      (PowerSeries.constantCoeff (R := K)).comp
          (PowerSeries.expand (R := K) N hN).toRingHom =
        PowerSeries.constantCoeff (R := K) := by
    apply RingHom.ext
    intro φ
    change PowerSeries.constantCoeff (PowerSeries.expand N hN φ) =
      PowerSeries.constantCoeff φ
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_expand]
    simp
  rw [hcomp, hgred] at hyc
  rw [Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at hyc
  apply sub_eq_zero.mp
  by_contra hne
  exact (pow_ne_zero m hne) hyc

/-- **Prescribed-edge Newton--Puiseux without ambient monicity.**  It is enough that the Newton
transform have a nonzero special fibre.  Hensel lifting first extracts the monic local factor
supported at the chosen edge root, after which ordinary Newton--Puiseux applies to that factor. -/
theorem exists_isRoot_map_expand_with_prescribed_newton_lead_of_specialFiber_ne
    [IsAlgClosed K] [CharZero K]
    {f : (PowerSeries K)[X]}
    (p q : ℕ) (hq : q ≠ 0)
    (hdvd : ∀ i ≤ f.natDegree,
      (PowerSeries.X : PowerSeries K) ^ (p * (f.natDegree - i)) ∣
        PowerSeries.expand q hq (f.coeff i))
    (c : K)
    (hfibne : (newtonTransform f p q hq).map
      (PowerSeries.constantCoeff (R := K)) ≠ 0)
    (hc : ((newtonTransform f p q hq).map
      (PowerSeries.constantCoeff (R := K))).IsRoot c) :
    ∃ (N : ℕ) (hN : N ≠ 0) (z : PowerSeries K),
      (f.map (PowerSeries.expand (R := K) (N * q) (Nat.mul_ne_zero hN hq)).toRingHom).IsRoot
        ((PowerSeries.X : PowerSeries K) ^ (N * p) * z) ∧
      PowerSeries.constantCoeff z = c := by
  classical
  let T : (PowerSeries K)[X] := newtonTransform f p q hq
  have hmpos : 0 < (T.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity c :=
    (Polynomial.rootMultiplicity_pos hfibne).2 hc
  obtain ⟨g, h, hgmonic, hgdeg, hTfactor, hgred⟩ :=
    exists_monic_factor_of_rootMultiplicity_with_reduction_of_specialFiber_ne hfibne c
  have hgpos : 0 < g.natDegree := by rw [hgdeg]; exact hmpos
  obtain ⟨N, hN, z, hz⟩ :=
    exists_isRoot_map_expand (K := K) g.natDegree g hgmonic rfl hgpos
  have hzT :
      (T.map (PowerSeries.expand (R := K) N hN).toRingHom).IsRoot z := by
    change ((newtonTransform f p q hq).map
      (PowerSeries.expand (R := K) N hN).toRingHom).IsRoot z
    rw [hTfactor, Polynomial.map_mul, Polynomial.IsRoot, Polynomial.eval_mul, hz, zero_mul]
  have hzlead : PowerSeries.constantCoeff z = c :=
    constantCoeff_eq_of_isRoot_map_expand_rootMultiplicity_factor hN hgred hz
  have hztransform :
      (newtonTransform f (N * p) (N * q) (Nat.mul_ne_zero hN hq)).IsRoot z := by
    rw [← map_expand_newtonTransform f p q N hq hN]
    exact hzT
  have hdvd' : ∀ i ≤ f.natDegree,
      (PowerSeries.X : PowerSeries K) ^ ((N * p) * (f.natDegree - i)) ∣
        PowerSeries.expand (N * q) (Nat.mul_ne_zero hN hq) (f.coeff i) := by
    intro i hi
    have hdiv := expand_dvd_X_pow hN (hdvd i hi)
    rw [← PowerSeries.expand_mul N hN q hq] at hdiv
    simpa only [Nat.mul_assoc] using hdiv
  refine ⟨N, hN, z, ?_, hzlead⟩
  exact isRoot_map_expand_of_isRoot_newtonTransform
    (N * p) (N * q) (Nat.mul_ne_zero hN hq) hdvd' hztransform

/-- **Newton--Puiseux with prescribed Newton-edge root.**  A chosen root `c` of the special fibre
of a Newton transform lifts, after a further nonzero ramification, to a root of the original
polynomial of the form `X^(N*p) * z`, with `z(0) = c`. -/
theorem exists_isRoot_map_expand_with_prescribed_newton_lead
    [IsAlgClosed K] [CharZero K]
    {f : (PowerSeries K)[X]} (hf : f.Monic)
    (p q : ℕ) (hq : q ≠ 0)
    (hdvd : ∀ i ≤ f.natDegree,
      (PowerSeries.X : PowerSeries K) ^ (p * (f.natDegree - i)) ∣
        PowerSeries.expand q hq (f.coeff i))
    (c : K)
    (hc : ((newtonTransform f p q hq).map
      (PowerSeries.constantCoeff (R := K))).IsRoot c) :
    ∃ (N : ℕ) (hN : N ≠ 0) (z : PowerSeries K),
      (f.map (PowerSeries.expand (R := K) (N * q) (Nat.mul_ne_zero hN hq)).toRingHom).IsRoot
        ((PowerSeries.X : PowerSeries K) ^ (N * p) * z) ∧
      PowerSeries.constantCoeff z = c := by
  classical
  let T : (PowerSeries K)[X] := newtonTransform f p q hq
  have hTmonic : T.Monic := (monic_newtonTransform hf p q hq).1
  have hTfibmonic : (T.map (PowerSeries.constantCoeff (R := K))).Monic := hTmonic.map _
  have hmpos : 0 < (T.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity c :=
    (Polynomial.rootMultiplicity_pos hTfibmonic.ne_zero).2 hc
  obtain ⟨g, h, hgmonic, _, hgdeg, hTfactor, hgred⟩ :=
    exists_monic_factor_of_rootMultiplicity_with_reduction hTmonic c
  have hgpos : 0 < g.natDegree := by rw [hgdeg]; exact hmpos
  obtain ⟨N, hN, z, hz⟩ :=
    exists_isRoot_map_expand (K := K) g.natDegree g hgmonic rfl hgpos
  have hzT :
      (T.map (PowerSeries.expand (R := K) N hN).toRingHom).IsRoot z := by
    rw [hTfactor, Polynomial.map_mul, Polynomial.IsRoot, Polynomial.eval_mul, hz, zero_mul]
  have hzlead : PowerSeries.constantCoeff z = c :=
    constantCoeff_eq_of_isRoot_map_expand_rootMultiplicity_factor hN hgred hz
  have hztransform :
      (newtonTransform f (N * p) (N * q) (Nat.mul_ne_zero hN hq)).IsRoot z := by
    rw [← map_expand_newtonTransform f p q N hq hN]
    exact hzT
  have hdvd' : ∀ i ≤ f.natDegree,
      (PowerSeries.X : PowerSeries K) ^ ((N * p) * (f.natDegree - i)) ∣
        PowerSeries.expand (N * q) (Nat.mul_ne_zero hN hq) (f.coeff i) := by
    intro i hi
    have hdiv := expand_dvd_X_pow hN (hdvd i hi)
    rw [← PowerSeries.expand_mul N hN q hq] at hdiv
    simpa only [Nat.mul_assoc] using hdiv
  refine ⟨N, hN, z, ?_, hzlead⟩
  exact isRoot_map_expand_of_isRoot_newtonTransform
    (N * p) (N * q) (Nat.mul_ne_zero hN hq) hdvd' hztransform

/-- **One common cover preserves every prescribed edge root in a finite family.**  The common
ramification `Q` is an exact multiple `M i * q i` of each initial edge denominator, and the
corresponding selected root has exponent `M i * p i` and leading coefficient `c i`. -/
theorem exists_isRoot_map_expand_finite_family_with_prescribed_newton_leads
    {K ι : Type} [Field K] [IsAlgClosed K] [CharZero K] [Fintype ι]
    (f : ι → (PowerSeries K)[X]) (hf : ∀ i, (f i).Monic)
    (p q : ι → ℕ) (hq : ∀ i, q i ≠ 0)
    (hdvd : ∀ i, ∀ j ≤ (f i).natDegree,
      (PowerSeries.X : PowerSeries K) ^ (p i * ((f i).natDegree - j)) ∣
        PowerSeries.expand (q i) (hq i) ((f i).coeff j))
    (c : ι → K)
    (hc : ∀ i, ((newtonTransform (f i) (p i) (q i) (hq i)).map
      (PowerSeries.constantCoeff (R := K))).IsRoot (c i)) :
    ∃ (Q : ℕ) (hQ : Q ≠ 0) (M : ι → ℕ) (z : ι → PowerSeries K),
      (∀ i, M i ≠ 0) ∧
      (∀ i, Q = M i * q i) ∧
      ∀ i,
        ((f i).map (PowerSeries.expand (R := K) Q hQ).toRingHom).IsRoot
          ((PowerSeries.X : PowerSeries K) ^ (M i * p i) * z i) ∧
        PowerSeries.constantCoeff (z i) = c i := by
  classical
  have hex : ∀ i, ∃ (N : ℕ) (hN : N ≠ 0) (z : PowerSeries K),
      ((f i).map
        (PowerSeries.expand (R := K) (N * q i) (Nat.mul_ne_zero hN (hq i))).toRingHom).IsRoot
          ((PowerSeries.X : PowerSeries K) ^ (N * p i) * z) ∧
      PowerSeries.constantCoeff z = c i := by
    intro i
    exact exists_isRoot_map_expand_with_prescribed_newton_lead
      (hf i) (p i) (q i) (hq i) (hdvd i) (c i) (hc i)
  let Ni : ι → ℕ := fun i => (hex i).choose
  have hNi : ∀ i, Ni i ≠ 0 := fun i => (hex i).choose_spec.choose
  let zi : ι → PowerSeries K := fun i => (hex i).choose_spec.choose_spec.choose
  have hyi : ∀ i,
      ((f i).map
        (PowerSeries.expand (R := K) (Ni i * q i) (Nat.mul_ne_zero (hNi i) (hq i))).toRingHom).IsRoot
          ((PowerSeries.X : PowerSeries K) ^ (Ni i * p i) * zi i) :=
    fun i => (hex i).choose_spec.choose_spec.choose_spec.1
  have hzi : ∀ i, PowerSeries.constantCoeff (zi i) = c i :=
    fun i => (hex i).choose_spec.choose_spec.choose_spec.2
  let Qi : ι → ℕ := fun i => Ni i * q i
  have hQi : ∀ i, Qi i ≠ 0 := fun i => Nat.mul_ne_zero (hNi i) (hq i)
  let Q : ℕ := ∏ i, Qi i
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hQi i
  let Ri : ι → ℕ := fun i => ∏ j ∈ Finset.univ.erase i, Qi j
  have hRi : ∀ i, Ri i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.mpr fun j _ => hQi j
  let M : ι → ℕ := fun i => Ri i * Ni i
  have hM : ∀ i, M i ≠ 0 := fun i => Nat.mul_ne_zero (hRi i) (hNi i)
  have hQfactor : ∀ i, Q = M i * q i := by
    intro i
    change (∏ j, Qi j) = (Ri i * Ni i) * q i
    rw [Nat.mul_assoc]
    change (∏ j, Qi j) = Ri i * Qi i
    exact (Finset.prod_erase_mul (s := Finset.univ) (f := Qi) (Finset.mem_univ i)).symm
  refine ⟨Q, hQ, M, fun i => PowerSeries.expand (R := K) (Ri i) (hRi i) (zi i),
    hM, hQfactor, ?_⟩
  intro i
  have hroot := isRoot_map_powerSeries
    (PowerSeries.expand (R := K) (Ri i) (hRi i)).toRingHom (hyi i)
  rw [Polynomial.map_map] at hroot
  have hcomp :
      (PowerSeries.expand (R := K) (Ri i) (hRi i)).toRingHom.comp
          (PowerSeries.expand (R := K) (Qi i) (hQi i)).toRingHom =
        (PowerSeries.expand (R := K) Q hQ).toRingHom := by
    apply RingHom.ext
    intro φ
    change PowerSeries.expand (R := K) (Ri i) (hRi i)
        (PowerSeries.expand (R := K) (Qi i) (hQi i) φ) =
      PowerSeries.expand (R := K) Q hQ φ
    have hprod : Q = Ri i * Qi i := by
      change (∏ j, Qi j) = Ri i * Qi i
      exact (Finset.prod_erase_mul (s := Finset.univ) (f := Qi) (Finset.mem_univ i)).symm
    simpa only [hprod] using
      (PowerSeries.expand_mul (Ri i) (hRi i) (Qi i) (hQi i) φ).symm
  have hvalue :
      PowerSeries.expand (R := K) (Ri i) (hRi i)
          ((PowerSeries.X : PowerSeries K) ^ (Ni i * p i) * zi i) =
        (PowerSeries.X : PowerSeries K) ^ (M i * p i) *
          PowerSeries.expand (R := K) (Ri i) (hRi i) (zi i) := by
    rw [map_mul, map_pow, PowerSeries.expand_X, ← pow_mul]
    congr 2
    change Ri i * (Ni i * p i) = (Ri i * Ni i) * p i
    exact (Nat.mul_assoc _ _ _).symm
  rw [hcomp] at hroot
  change ((f i).map (PowerSeries.expand (R := K) Q hQ).toRingHom).IsRoot
    (PowerSeries.expand (R := K) (Ri i) (hRi i)
      ((PowerSeries.X : PowerSeries K) ^ (Ni i * p i) * zi i)) at hroot
  rw [hvalue] at hroot
  refine ⟨hroot, ?_⟩
  change PowerSeries.constantCoeff
      (PowerSeries.expand (R := K) (Ri i) (hRi i) (zi i)) = c i
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_expand]
  simpa using hzi i

end GaloisForLFunctions.HTGeometry
