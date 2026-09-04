import GaloisForLFunctions.HTGeometry.FirstOrderWimanInfinityPowerSeries

/-!
# Actual prescribed Puiseux root of every Wiman top symbol

The signed rational Wiman slope is cleared into natural exponents, the exact maximal edge is
identified as the special fibre of a power-series polynomial, and nonmonic prescribed-root
Newton--Puiseux lifting produces an actual ramified root with the selected nonzero coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

noncomputable section

/-- Every rational number is a difference of natural exponents divided by a positive natural
denominator.  This is the pole/zero split used at `U = ∞`. -/
theorem exists_natural_signed_fraction (p : ℚ) :
    ∃ M a q : ℕ, q ≠ 0 ∧ p = ((M : ℚ) - (a : ℚ)) / q := by
  rcases le_total 0 p.num with hnum | hnum
  · refine ⟨p.num.toNat, 0, p.den, p.den_nz, ?_⟩
    calc
      p = (p.num : ℚ) / (p.den : ℚ) := (Rat.num_div_den p).symm
      _ = (p.num.toNat : ℚ) / (p.den : ℚ) := by
        congr 1
        exact_mod_cast (Int.toNat_of_nonneg hnum).symm
      _ = (((p.num.toNat : ℕ) : ℚ) - (0 : ℚ)) / (p.den : ℚ) := by ring
  · refine ⟨0, (-p.num).toNat, p.den, p.den_nz, ?_⟩
    have hcast : (p.num : ℚ) = -(((-p.num).toNat : ℕ) : ℚ) := by
      exact_mod_cast (show p.num = -(((-p.num).toNat : ℕ) : ℤ) by
        rw [Int.toNat_of_nonneg (Int.neg_nonneg.mpr hnum), Int.neg_neg])
    calc
      p = (p.num : ℚ) / (p.den : ℚ) := (Rat.num_div_den p).symm
      _ = (-(((-p.num).toNat : ℕ) : ℚ)) / (p.den : ℚ) := by rw [hcast]
      _ = ((0 : ℚ) - ((-p.num).toNat : ℚ)) / (p.den : ℚ) := by ring

private theorem naturalBoundary_le_of_rationalWeight_le
    (p : ℚ) (M a q m di d₀ ki k₀ : ℕ) (hq : q ≠ 0)
    (hp : p = ((M : ℚ) - (a : ℚ)) / q)
    (hki : ki ≤ m) (hk₀ : k₀ ≤ m)
    (hw : (di : ℚ) + (ki : ℚ) * p ≤ (d₀ : ℚ) + (k₀ : ℚ) * p) :
    q * di + M * ki + a * (m - ki) ≤ q * d₀ + M * k₀ + a * (m - k₀) := by
  have hqi :
      ((q * di + M * ki + a * (m - ki) : ℕ) : ℚ) =
        (q : ℚ) * ((di : ℚ) + (ki : ℚ) * p) + (a : ℚ) * m := by
    rw [hp, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub hki]
    field_simp [hq]
    ring
  have hq₀ :
      ((q * d₀ + M * k₀ + a * (m - k₀) : ℕ) : ℚ) =
        (q : ℚ) * ((d₀ : ℚ) + (k₀ : ℚ) * p) + (a : ℚ) * m := by
    rw [hp, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub hk₀]
    field_simp [hq]
    ring
  exact_mod_cast (show
    ((q * di + M * ki + a * (m - ki) : ℕ) : ℚ) ≤
      ((q * d₀ + M * k₀ + a * (m - k₀) : ℕ) : ℚ) by
        rw [hqi, hq₀]
        gcongr)

private theorem naturalBoundary_eq_iff_rationalWeight_eq
    (p : ℚ) (M a q m di d₀ ki k₀ : ℕ) (hq : q ≠ 0)
    (hp : p = ((M : ℚ) - (a : ℚ)) / q)
    (hki : ki ≤ m) (hk₀ : k₀ ≤ m) :
    q * di + M * ki + a * (m - ki) = q * d₀ + M * k₀ + a * (m - k₀) ↔
      (di : ℚ) + (ki : ℚ) * p = (d₀ : ℚ) + (k₀ : ℚ) * p := by
  have hqi :
      ((q * di + M * ki + a * (m - ki) : ℕ) : ℚ) =
        (q : ℚ) * ((di : ℚ) + (ki : ℚ) * p) + (a : ℚ) * m := by
    rw [hp, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub hki]
    field_simp [hq]
    ring
  have hq₀ :
      ((q * d₀ + M * k₀ + a * (m - k₀) : ℕ) : ℚ) =
        (q : ℚ) * ((d₀ : ℚ) + (k₀ : ℚ) * p) + (a : ℚ) * m := by
    rw [hp, Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub hk₀]
    field_simp [hq]
    ring
  constructor
  · intro h
    have hcast := congrArg (fun n : ℕ => (n : ℚ)) h
    rw [hqi, hq₀] at hcast
    have hqpos : (0 : ℚ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    nlinarith
  · intro h
    exact_mod_cast (show
      ((q * di + M * ki + a * (m - ki) : ℕ) : ℚ) =
        ((q * d₀ + M * k₀ + a * (m - k₀) : ℕ) : ℚ) by
          rw [hqi, hq₀, h])

/-- **Prescribed Wiman top-symbol root.**  Every exact initial-data package yields one literal
power-series compactification whose Newton transform has precisely the chosen Wiman edge as its
special fibre, and an actual root on a finite ramified cover with the prescribed edge coefficient.
The parameters encode `U = s⁻q`, `T = s⁻M Y`, and `Y = sᵃ z`. -/
theorem exists_entireFirstOrderWiman_topSymbolPuiseuxRoot
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    ∃ (M a q m H N : ℕ) (hN : N ≠ 0) (z : PowerSeries ℂ),
      q ≠ 0 ∧ data.slope = ((M : ℚ) - (a : ℚ)) / q ∧
      let F := firstOrderInfinityPowerSeriesPolynomial data.indexSupport data.coeff
        data.totalDegree q M H
      (∀ i ∈ firstOrderTopNewtonFace data.indexSupport data.coeff data.totalDegree,
          ∀ n ∈ (data.coeff i).support, q * n + M * i.2 ≤ H) ∧
      F.natDegree = m ∧
      (newtonTransform F a 1 one_ne_zero).map
          (PowerSeries.constantCoeff (R := ℂ)) =
        firstOrderNewtonEdgePolynomial
          (firstOrderMaxNewtonFace data.indexSupport data.coeff data.totalDegree
            (data.slope : ℝ)
            (firstOrderNewtonWeight data.coeff (data.slope : ℝ) data.firstIndex)) data.coeff ∧
      (F.map (PowerSeries.expand (R := ℂ) N hN).toRingHom).IsRoot
          ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z) ∧
      PowerSeries.constantCoeff z = data.root := by
  classical
  let top := firstOrderTopNewtonFace data.indexSupport data.coeff data.totalDegree
  have hfirstTop : data.firstIndex ∈ top :=
    (Finset.mem_filter.mp data.first_mem_face).1
  obtain ⟨iMax, hiMax, hiMaximal⟩ :=
    Finset.exists_max_image top Prod.snd ⟨data.firstIndex, hfirstTop⟩
  obtain ⟨M, a, q, hq, hp⟩ := exists_natural_signed_fraction data.slope
  let m := iMax.2
  have hm : ∀ i ∈ top, i.2 ≤ m := fun i hi => hiMaximal i hi
  have hfirstLe : data.firstIndex.2 ≤ m := hm data.firstIndex hfirstTop
  let H := q * (data.coeff data.firstIndex).natDegree + M * data.firstIndex.2 +
    a * (m - data.firstIndex.2)
  let F := firstOrderInfinityPowerSeriesPolynomial data.indexSupport data.coeff
    data.totalDegree q M H
  have hnaturalBound : ∀ i ∈ top,
      q * (data.coeff i).natDegree + M * i.2 + a * (m - i.2) ≤ H := by
    intro i hi
    have hwReal :
        firstOrderNewtonWeight data.coeff (data.slope : ℝ) i ≤
          firstOrderNewtonWeight data.coeff (data.slope : ℝ) data.firstIndex := by
      calc
        firstOrderNewtonWeight data.coeff (data.slope : ℝ) i ≤ data.weight :=
          data.weight_maximal i hi
        _ = firstOrderNewtonWeight data.coeff (data.slope : ℝ) data.firstIndex :=
          (Finset.mem_filter.mp data.first_mem_face).2.symm
    have hwRat :
        ((data.coeff i).natDegree : ℚ) + (i.2 : ℚ) * data.slope ≤
          ((data.coeff data.firstIndex).natDegree : ℚ) +
            (data.firstIndex.2 : ℚ) * data.slope := by
      rw [firstOrderNewtonWeight, firstOrderNewtonWeight] at hwReal
      exact_mod_cast hwReal
    simpa only [H] using naturalBoundary_le_of_rationalWeight_le data.slope M a q m
      (data.coeff i).natDegree (data.coeff data.firstIndex).natDegree i.2
      data.firstIndex.2 hq hp (hm i hi) hfirstLe hwRat
  have hbaseMax : q * (data.coeff iMax).natDegree + M * iMax.2 ≤ H := by
    have h := hnaturalBound iMax hiMax
    simp only [m, Nat.sub_self, mul_zero, add_zero] at h
    exact h
  have hdegree : F.natDegree = m := by
    exact natDegree_firstOrderInfinityPowerSeriesPolynomial_eq_maxDerivative
      data.indexSupport data.coeff data.totalDegree q M H iMax hiMax
      (fun i hi => hm i hi) hq hbaseMax
  have hclearBound : ∀ i ∈ top, ∀ n ∈ (data.coeff i).support,
      q * n + M * i.2 ≤ H := by
    intro i hi n hn
    have hnle := Polynomial.le_natDegree_of_mem_supp n hn
    calc
      q * n + M * i.2 ≤ q * (data.coeff i).natDegree + M * i.2 := by gcongr
      _ ≤ q * (data.coeff i).natDegree + M * i.2 + a * (m - i.2) :=
        Nat.le_add_right _ _
      _ ≤ H := hnaturalBound i hi
  have hrowBound : ∀ i ∈ top, ∀ n ∈ (data.coeff i).support,
      a * (m - i.2) ≤ H - (q * n + M * i.2) := by
    intro i hi n hn
    have hnle := Polynomial.le_natDegree_of_mem_supp n hn
    have hbase : q * n + M * i.2 + a * (m - i.2) ≤ H := by
      calc
        q * n + M * i.2 + a * (m - i.2) ≤
            q * (data.coeff i).natDegree + M * i.2 + a * (m - i.2) := by gcongr
        _ ≤ H := hnaturalBound i hi
    omega
  have hdvd : ∀ k ≤ F.natDegree,
      (PowerSeries.X : PowerSeries ℂ) ^ (a * (F.natDegree - k)) ∣ F.coeff k := by
    exact X_pow_dvd_coeff_firstOrderInfinityPowerSeriesPolynomial
      data.indexSupport data.coeff data.totalDegree q M H m a hdegree hrowBound
  have hface : ∀ i ∈ top,
      (q * (data.coeff i).natDegree + M * i.2 + a * (m - i.2) = H ↔
        firstOrderNewtonWeight data.coeff (data.slope : ℝ) i =
          firstOrderNewtonWeight data.coeff (data.slope : ℝ) data.firstIndex) := by
    intro i hi
    have hnat := naturalBoundary_eq_iff_rationalWeight_eq data.slope M a q m
      (data.coeff i).natDegree (data.coeff data.firstIndex).natDegree i.2
      data.firstIndex.2 hq hp (hm i hi) hfirstLe
    change
      (q * (data.coeff i).natDegree + M * i.2 + a * (m - i.2) =
          q * (data.coeff data.firstIndex).natDegree + M * data.firstIndex.2 +
            a * (m - data.firstIndex.2) ↔ _)
    rw [hnat]
    constructor
    · intro h
      rw [firstOrderNewtonWeight, firstOrderNewtonWeight]
      exact_mod_cast h
    · intro h
      rw [firstOrderNewtonWeight, firstOrderNewtonWeight] at h
      exact_mod_cast h
  have hspecial :
      (newtonTransform F a 1 one_ne_zero).map
          (PowerSeries.constantCoeff (R := ℂ)) =
        firstOrderNewtonEdgePolynomial
          (firstOrderMaxNewtonFace data.indexSupport data.coeff data.totalDegree
            (data.slope : ℝ)
            (firstOrderNewtonWeight data.coeff (data.slope : ℝ) data.firstIndex)) data.coeff := by
    change (newtonTransform
      (firstOrderInfinityPowerSeriesPolynomial data.indexSupport data.coeff
        data.totalDegree q M H) a 1 one_ne_zero).map
          (PowerSeries.constantCoeff (R := ℂ)) = _
    rw [specialFiber_newtonTransform_firstOrderInfinityPowerSeriesPolynomial
      data.indexSupport data.coeff data.totalDegree q M H m a hdegree hq
      (fun i hi => hm i hi) hnaturalBound]
    exact firstOrderInfinityNaturalEdgePolynomial_eq_newtonEdge
      data.indexSupport data.coeff data.totalDegree q M H m a
      (data.slope : ℝ)
      (firstOrderNewtonWeight data.coeff (data.slope : ℝ) data.firstIndex) hface
  have hfibne : (newtonTransform F a 1 one_ne_zero).map
      (PowerSeries.constantCoeff (R := ℂ)) ≠ 0 := by
    rw [hspecial]
    apply firstOrderNewtonEdgePolynomial_ne_zero_of_mem
      data.indexSupport data.coeff data.totalDegree
      (firstOrderMaxNewtonFace data.indexSupport data.coeff data.totalDegree
        (data.slope : ℝ)
        (firstOrderNewtonWeight data.coeff (data.slope : ℝ) data.firstIndex))
      (Finset.filter_subset _ _) data.firstIndex
    have hweight := (Finset.mem_filter.mp data.first_mem_face).2
    rw [hweight]
    exact data.first_mem_face
  have hc : ((newtonTransform F a 1 one_ne_zero).map
      (PowerSeries.constantCoeff (R := ℂ))).IsRoot data.root := by
    rw [hspecial]
    have hweight := (Finset.mem_filter.mp data.first_mem_face).2
    rw [hweight]
    exact data.edge_root
  have hexpandOne : ∀ φ : PowerSeries ℂ,
      PowerSeries.expand 1 one_ne_zero φ = φ := by
    intro φ
    ext n
    rw [PowerSeries.coeff_expand]
    simp
  have hdvdOne : ∀ k ≤ F.natDegree,
      (PowerSeries.X : PowerSeries ℂ) ^ (a * (F.natDegree - k)) ∣
        PowerSeries.expand 1 one_ne_zero (F.coeff k) := by
    intro k hk
    rw [hexpandOne]
    exact hdvd k hk
  obtain ⟨N, hN, z, hroot, hz⟩ :=
    exists_isRoot_map_expand_with_prescribed_newton_lead_of_specialFiber_ne
      a 1 one_ne_zero hdvdOne data.root hfibne hc
  refine ⟨M, a, q, m, H, N, hN, z, hq, hp, hclearBound, hdegree, hspecial, ?_, hz⟩
  simpa only [Nat.mul_one] using hroot

end

end GaloisForLFunctions.HTGeometry
