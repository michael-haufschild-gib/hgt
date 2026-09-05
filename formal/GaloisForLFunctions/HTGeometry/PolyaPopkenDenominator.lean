import GaloisForLFunctions.HTGeometry.MahlerDenominatorSeries
import GaloisForLFunctions.HTGeometry.MahlerCoefficientFieldConfinement

/-!
# Pólya's denominator bound for the coefficients of an algebraic differential equation

The coefficients of a formal solution of a nondegenerate Euler differential equation with
bounded-denominator coefficients have denominators dividing the Mahler weight
`C^q ∏_{j ≤ q} A_j^{⌊q/j⌋}`, where `A_j` is the absolute norm of the `j`-th value of the indicial
polynomial.  The floor exponents make the weight superadditive, which is exactly what the
convolution in the nonlinear part of the recursion needs.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-! ### Bounded denominators of the auxiliary series -/

theorem mahlerScale_trivial (q : ℕ) : mahlerScale 1 (fun _ => 1) q = 1 := by
  simp [mahlerScale]

theorem boundedDen_iff {X : PowerSeries ℂ} :
    BoundedDenSeries X ↔ ∃ e : ℕ, 0 < e ∧ MahlerDen 1 (fun _ => 1) 0 e X := by
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, mahlerDen_of_boundedDen h⟩
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, fun n => ?_⟩
    have := h.den n
    simpa [mahlerScale_trivial] using this

theorem BoundedDenSeries.add {X Z : PowerSeries ℂ} (hX : BoundedDenSeries X)
    (hZ : BoundedDenSeries Z) : BoundedDenSeries (X + Z) :=
  boundedDenSubsemiring.add_mem hX hZ

theorem BoundedDenSeries.mul {X Z : PowerSeries ℂ} (hX : BoundedDenSeries X)
    (hZ : BoundedDenSeries Z) : BoundedDenSeries (X * Z) :=
  boundedDenSubsemiring.mul_mem hX hZ

theorem BoundedDenSeries.eulerOp {X : PowerSeries ℂ} (hX : BoundedDenSeries X) :
    BoundedDenSeries (formalEulerOp X) := by
  obtain ⟨e, he, h⟩ := hX
  exact ⟨e, he, fun n => by
    rw [coeff_formalEulerOp]
    exact DenBy.natMul n (h n)⟩

theorem BoundedDenSeries.eulerJet {m : ℕ} {X : PowerSeries ℂ} (hX : BoundedDenSeries X)
    (j : Fin (m + 1)) : BoundedDenSeries (eulerJetVector (m := m) X j) := by
  obtain ⟨e, he, h⟩ := hX
  refine ⟨e, he, fun n => ?_⟩
  have hm : MahlerDen 1 (fun _ => 1) 0 e X := mahlerDen_of_boundedDen h
  have := (MahlerDen.eulerJet (C := 1) (A := fun _ => 1) hm j).den n
  simpa [mahlerScale_trivial] using this

theorem BoundedDenSeries.aeval {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → PowerSeries ℂ}
    (hS : ∀ i, BoundedDenSeries (S i)) (Q : MvPolynomial ι (PowerSeries ℂ))
    (hQ : ∀ d, BoundedDenSeries (MvPolynomial.coeff d Q)) :
    BoundedDenSeries (MvPolynomial.aeval S Q) := by
  classical
  obtain ⟨eQ, heQ, hQd⟩ := exists_uniform_coeff_den Q hQ
  choose eS heS hSd using hS
  set e : ℕ := eQ * ∏ i : ι, eS i with hedef
  have he : 0 < e := mul_pos heQ (Finset.prod_pos fun i _ => heS i)
  have hSm : ∀ i, MahlerDen 1 (fun _ => 1) 0 e (S i) := by
    intro i
    refine mahlerDen_of_boundedDen fun n => (hSd i n).mono ?_
    refine Dvd.dvd.mul_left ?_ eQ
    exact Finset.dvd_prod_of_mem eS (Finset.mem_univ i)
  have hQm : ∀ d, MahlerDen 1 (fun _ => 1) 0 e (MvPolynomial.coeff d Q) := by
    intro d
    refine mahlerDen_of_boundedDen fun n => (hQd d n).mono ?_
    exact Dvd.intro _ rfl
  have := MahlerDen.aeval (C := 1) (A := fun _ => 1) hSm Q hQm
  refine ⟨e ^ (1 + Q.totalDegree), by positivity, fun n => ?_⟩
  have h2 := this.den n
  simpa [mahlerScale_trivial] using h2

theorem boundedDen_pderiv {ι : Type*} [DecidableEq ι] {Q : MvPolynomial ι (PowerSeries ℂ)}
    (hQ : ∀ d, BoundedDenSeries (MvPolynomial.coeff d Q)) (j : ι) :
    ∀ d, BoundedDenSeries (MvPolynomial.coeff d (MvPolynomial.pderiv j Q)) := by
  intro d
  obtain ⟨e, he, h⟩ := hQ (d + Finsupp.single j 1)
  refine ⟨e, he, fun n => ?_⟩
  rw [MvPolynomial.coeff_pderiv, mul_comm, ← Nat.cast_one, ← Nat.cast_add, ← nsmul_eq_mul,
    map_nsmul, nsmul_eq_mul]
  exact DenBy.natMul _ (h n)

theorem boundedDen_truncPowerSeries {F : PowerSeries ℂ}
    (halg : ∀ n, IsAlgebraic ℚ (PowerSeries.coeff n F)) (N : ℕ) :
    BoundedDenSeries (truncPowerSeries N F) := by
  classical
  choose d hd hdd using fun n => exists_denBy (halg n)
  refine ⟨∏ n ∈ Finset.range (N + 1), d n, Finset.prod_pos fun n _ => hd n, fun n => ?_⟩
  rw [coeff_truncPowerSeries]
  split_ifs with hn
  · exact (hdd n).mono (Finset.dvd_prod_of_mem d (Finset.mem_range.mpr (by omega)))
  · simp

/-! ### The denominator recursion -/

/-- **Pólya's denominator bound.**  For a nondegenerate Euler differential equation with
bounded-denominator coefficients, the denominators of the coefficients of a formal solution divide
the Mahler weight built from any denominators `A q` of the inverse indicial values. -/
theorem exists_mahlerDen_of_nondegenerate_eulerADE
    {m : ℕ} (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : ∀ d, BoundedDenSeries (MvPolynomial.coeff d P))
    (K : IntermediateField ℚ ℂ)
    (hPK : ∀ d, CoefficientsIn K (MvPolynomial.coeff d P))
    {F : PowerSeries ℂ} (halg : ∀ n, IsAlgebraic ℚ (PowerSeries.coeff n F))
    (hFK : CoefficientsIn K F)
    (hsol : IsFormalEulerADESolution P F)
    (hnd : ∃ j, MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j P) ≠ 0) :
    ∃ (N e : ℕ) (b : Fin (m + 1) → ℂ), 0 < e ∧ (∀ i, b i ∈ K) ∧
      (∀ q, 1 ≤ q →
        (∑ i : Fin (m + 1), b i * ((q + N : ℕ) : ℂ) ^ (i : ℕ)) ≠ 0) ∧
      ∀ (C : ℕ) (A : ℕ → ℕ), 0 < C → (∀ q, 0 < A q) → e ∣ C →
        (∀ q, 1 ≤ q → IsIntegral ℤ ((A q : ℂ) /
          ∑ i : Fin (m + 1), b i * ((q + N : ℕ) : ℂ) ^ (i : ℕ))) →
        ∀ n, DenBy (e * mahlerScale C A (n - N)) (PowerSeries.coeff n F) := by
  classical
  set Bf : Fin (m + 1) → PowerSeries ℂ :=
    fun j => MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j P) with hBfdef
  obtain ⟨j0, hj0⟩ := hnd
  have hex : ∃ μ, shiftPolynomial Bf μ ≠ 0 := by
    obtain ⟨μ, hμ⟩ : ∃ μ, PowerSeries.coeff μ (Bf j0) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hj0 (PowerSeries.ext hc)
    exact ⟨μ, shiftPolynomial_ne_zero_of_coeff hμ⟩
  set v : ℕ := Nat.find hex with hvdef
  have hv : shiftPolynomial Bf v ≠ 0 := Nat.find_spec hex
  have hvlow : ∀ μ, μ < v → shiftPolynomial Bf μ = 0 := by
    intro μ hμ
    by_contra hc
    exact absurd hμ (not_lt.mpr (Nat.find_le hc))
  obtain ⟨N0, hN0⟩ := GaloisForLFunctions.poly_eventually_ne_zero_nat
    (shiftPolynomial Bf v) hv
  set N : ℕ := max v N0 + 1 with hNdef
  have hvN : v < N := by omega
  have hN0N : N0 ≤ N := by omega
  set Y : PowerSeries ℂ := truncPowerSeries N F with hYdef
  set H : PowerSeries ℂ := F - Y with hHdef
  set B : Fin (m + 1) → PowerSeries ℂ := linearizationCoeff P Y with hBdef
  -- the coefficients of the truncation
  have hYmem : CoefficientsIn K Y := by
    intro n
    rw [hYdef, coeff_truncPowerSeries]
    split_ifs with hn
    · exact hFK n
    · exact K.zero_mem
  have hYbd : BoundedDenSeries Y := boundedDen_truncPowerSeries halg N
  have hagree : ∀ μ, μ ≤ N → shiftPolynomial B μ = shiftPolynomial Bf μ := by
    intro μ hμ
    rw [shiftPolynomial, shiftPolynomial]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    rw [hBdef, linearizationCoeff, hYdef, hBfdef]
    exact coeff_aeval_eulerJetVector_truncPowerSeries_eq (MvPolynomial.pderiv j P) F hμ
  have hBlow : ∀ μ, μ < v → shiftPolynomial B μ = 0 := by
    intro μ hμ
    rw [hagree μ (by omega)]
    exact hvlow μ hμ
  set b : Fin (m + 1) → ℂ := fun i => PowerSeries.coeff v (B i) with hbdef
  have hbK : ∀ i, b i ∈ K := by
    intro i
    exact coeff_linearizationCoeff_mem K P hPK hYmem i v
  have hLeval : ∀ n : ℕ, (shiftPolynomial B v).eval ((n : ℕ) : ℂ)
      = ∑ i : Fin (m + 1), b i * ((n : ℕ) : ℂ) ^ (i : ℕ) := by
    intro n
    rw [eval_shiftPolynomial]
  have hLne : ∀ q, 1 ≤ q → (∑ i : Fin (m + 1), b i * ((q + N : ℕ) : ℂ) ^ (i : ℕ)) ≠ 0 := by
    intro q hq
    rw [← hLeval (q + N), hagree v (by omega)]
    exact hN0 (q + N) (by omega)
  -- the constants of the recursion
  obtain ⟨eY, heY, hYd⟩ := hYbd
  have hBbd : ∀ i, BoundedDenSeries (B i) := by
    intro i
    rw [hBdef, linearizationCoeff]
    exact BoundedDenSeries.aeval (fun j => BoundedDenSeries.eulerJet ⟨eY, heY, hYd⟩ j)
      (MvPolynomial.pderiv i P) (boundedDen_pderiv hP i)
  obtain ⟨eB, heB, hBd⟩ : ∃ e : ℕ, 0 < e ∧ ∀ i n, DenBy e (PowerSeries.coeff n (B i)) := by
    choose ei hei hid using hBbd
    refine ⟨∏ i : Fin (m + 1), ei i, Finset.prod_pos fun i _ => hei i, fun i n => ?_⟩
    exact (hid i n).mono (Finset.dvd_prod_of_mem ei (Finset.mem_univ i))
  obtain ⟨eV, heV, hVd⟩ : BoundedDenSeries (MvPolynomial.aeval (eulerJetVector Y) P) :=
    BoundedDenSeries.aeval (fun j => BoundedDenSeries.eulerJet ⟨eY, heY, hYd⟩ j) P hP
  obtain ⟨eD, heD, hDprop⟩ := exists_taylorDefect_const P hP N eY heY
  refine ⟨N, eY * eB * eV * eD, b, by positivity, hbK, hLne, ?_⟩
  intro C A hC hApos hediv hAinv
  have hHvanish : ∀ k, k ≤ N → PowerSeries.coeff k H = 0 := by
    intro k hk
    rw [hHdef, hYdef, map_sub, coeff_truncPowerSeries, if_pos hk, sub_self]
  have hHdvd : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ H := by
    rw [hHdef, hYdef]
    exact X_pow_dvd_sub_truncPowerSeries N F
  have hYH : Y + H = F := by rw [hHdef]; ring
  have hsol' : IsFormalEulerADESolution P (Y + H) := by rw [hYH]; exact hsol
  have hLH : eulerLinearOp B H =
      -(MvPolynomial.aeval (eulerJetVector Y) P)
        - taylorDefect (eulerJetVector Y) (eulerJetVector H) P := by
    rw [hBdef]
    exact eulerLinearOp_linearization_eq P Y H hsol'
  have hHmem : ∀ n, DenBy (mahlerScale C A (n - N)) (PowerSeries.coeff n H) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n ≤ N
      · rw [hHvanish n hn]
        simp
      · have hnN : N < n := Nat.lt_of_not_ge hn
        have hq1 : 1 ≤ n - N := by omega
        set H' : PowerSeries ℂ := truncPowerSeries (n - 1) H with hH'def
        have hH'mahler : MahlerDen C A N 1 H' := by
          constructor
          · intro k hk
            rw [hH'def, coeff_truncPowerSeries]
            split_ifs with hk'
            · exact hHvanish k (by omega)
            · rfl
          · intro k
            rw [hH'def, coeff_truncPowerSeries]
            split_ifs with hk'
            · simpa using ih k (by omega)
            · simp
        have hSm : ∀ i, MahlerDen C A 0 eY (eulerJetVector (m := m) Y i) := fun i =>
          MahlerDen.eulerJet (mahlerDen_of_boundedDen hYd) i
        have hLm : ∀ i, MahlerDen C A N eY (eulerJetVector (m := m) H' i) := fun i =>
          MahlerDen.eulerJet (hH'mahler.mono_const (one_dvd _)) i
        have hDef := hDprop C A (eulerJetVector Y) (eulerJetVector H') hSm hLm
        have hH'dvd : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ H' := by
          rw [hH'def]
          exact X_pow_dvd_truncPowerSeries hHdvd
        have hdiff : (PowerSeries.X : PowerSeries ℂ) ^ n ∣ (H - H') := by
          rw [hH'def]
          simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
            (X_pow_dvd_sub_truncPowerSeries (n - 1) H)
        have hdefeq := coeff_taylorDefect_eq_of_sub_dvd P Y H H' (j := n + v) (by omega)
          hHdvd hH'dvd hdiff
        have hdefden : DenBy (eD * mahlerScale C A (n - N - 1))
            (PowerSeries.coeff (n + v)
              (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)) := by
          rw [hdefeq]
          refine (hDef.den (n + v)).mono (mul_dvd_mul_left eD ?_)
          exact mahlerScale_dvd_of_le C A (by omega)
        have hVden : DenBy (eV * mahlerScale C A (n - N - 1))
            (PowerSeries.coeff (n + v) (MvPolynomial.aeval (eulerJetVector Y) P)) :=
          (hVd (n + v)).mono (dvd_mul_right eV _)
        have hlinden : DenBy (eV * eD * mahlerScale C A (n - N - 1))
            (PowerSeries.coeff (n + v) (eulerLinearOp B H)) := by
          rw [hLH, map_sub, map_neg]
          refine DenBy.sub (DenBy.neg (hVden.mono ?_)) (hdefden.mono ?_)
          · exact mul_dvd_mul_right (dvd_mul_right eV eD) _
          · exact mul_dvd_mul_right (dvd_mul_left eD eV) _
        have htailden : DenBy (eB * mahlerScale C A (n - N - 1))
            (∑ k ∈ Finset.range n, (shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ) *
              PowerSeries.coeff k H) := by
          refine DenBy.sum ?_
          intro k hk
          have hkn : k < n := Finset.mem_range.mp hk
          have h1 : DenBy eB ((shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)) := by
            rw [eval_shiftPolynomial]
            refine DenBy.sum ?_
            intro i _
            have hrw : PowerSeries.coeff (n + v - k) (B i) * ((k : ℕ) : ℂ) ^ (i : ℕ)
                = (((k ^ (i : ℕ) : ℕ)) : ℂ) * PowerSeries.coeff (n + v - k) (B i) := by
              push_cast
              ring
            rw [hrw]
            exact DenBy.natMul _ (hBd i _)
          have h2 : DenBy (mahlerScale C A (k - N)) (PowerSeries.coeff k H) := ih k hkn
          refine (DenBy.mul h1 h2).mono (mul_dvd_mul_left eB ?_)
          exact mahlerScale_dvd_of_le C A (by omega)
        have hrec := shiftPolynomial_shift_mul_coeff B v hBlow H n
        have hprodden : DenBy (eV * eD * eB * mahlerScale C A (n - N - 1))
            ((shiftPolynomial B v).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n H) := by
          rw [hrec]
          refine DenBy.sub (hlinden.mono ?_) (htailden.mono ?_)
          · exact mul_dvd_mul_right (dvd_mul_right (eV * eD) eB) _
          · exact mul_dvd_mul_right (dvd_mul_left eB (eV * eD)) _
        have hLval : (shiftPolynomial B v).eval ((n : ℕ) : ℂ)
            = ∑ i : Fin (m + 1), b i * (((n - N) + N : ℕ) : ℂ) ^ (i : ℕ) := by
          rw [hLeval n]
          have hnn : ((n - N) + N : ℕ) = n := by omega
          rw [hnn]
        have hLne' : (shiftPolynomial B v).eval ((n : ℕ) : ℂ) ≠ 0 := by
          rw [hLval]
          exact hLne (n - N) hq1
        have hAint := hAinv (n - N) hq1
        rw [← hLval] at hAint
        have hstep : DenBy (A (n - N) * (eV * eD * eB) * mahlerScale C A (n - N - 1))
            (PowerSeries.coeff n H) := by
          have hkey : ((A (n - N) * (eV * eD * eB) * mahlerScale C A (n - N - 1) : ℕ) : ℂ) *
              PowerSeries.coeff n H
              = ((A (n - N) : ℂ) / (shiftPolynomial B v).eval ((n : ℕ) : ℂ)) *
                (((eV * eD * eB * mahlerScale C A (n - N - 1) : ℕ) : ℂ) *
                  ((shiftPolynomial B v).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n H)) := by
            field_simp
            push_cast
            ring
          unfold DenBy
          rw [hkey]
          exact hAint.mul hprodden
        refine hstep.mono ?_
        have hCdvd : eV * eD * eB ∣ C := by
          refine dvd_trans ?_ hediv
          exact ⟨eY, by ring⟩
        obtain ⟨c, hc⟩ := hCdvd
        obtain ⟨k, hk⟩ := mahlerScale_succ_dvd C A hq1
        refine ⟨c * k, ?_⟩
        calc mahlerScale C A (n - N)
            = C * A (n - N) * mahlerScale C A (n - N - 1) * k := hk
          _ = A (n - N) * (eV * eD * eB) * mahlerScale C A (n - N - 1) * (c * k) := by
              rw [hc]; ring
  intro n
  rw [← hYH, map_add]
  refine DenBy.add ?_ ?_
  · refine (hYd n).mono ?_
    refine dvd_trans ?_ (dvd_mul_right (eY * eB * eV * eD) (mahlerScale C A (n - N)))
    exact dvd_trans (dvd_mul_right eY eB) (dvd_trans (dvd_mul_right (eY * eB) eV)
      (dvd_mul_right (eY * eB * eV) eD))
  · exact (hHmem n).mono (dvd_mul_left _ _)

end GaloisForLFunctions.HTGeometry
