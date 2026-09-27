import GaloisForLFunctions.HTGeometry.FirstOrderWimanTerminalPuiseuxRoot

/-!
# Slope-one Laurent branches of a first-order relation over any coefficient field

Let `P = ∑_{i ∈ S} A_i(U) V^(i₁) W^(i₂)` be a first-order relation of total `(V,W)`-degree at most
`d`, and let `Q(U,T) = ∑_{i₁+i₂=d} A_i(U) T^(i₂)` be its top symbol.  Over an arbitrary
algebraically closed field `K` of characteristic zero containing `ℂ`, fix a value `u ∈ K` of the
first coordinate and a root `σ` of `Q(u,·)`.  Then, after a finite ramification `V = t^(-R)`, the
relation has the Laurent root

`W = t^(-R) z(t)`,   `z(0) = σ`.

The root is the Newton--Puiseux lift of `σ` for `t^d P(u, t^(-1), t^(-1) Y)`, a polynomial over
`K[[t]]` whose special fibre is exactly `Q(u, Y)`.  This is the terminal step of the corpus's
two-stage Wiman branch, with the coefficient field and the value `u` left arbitrary, as the
bottom-up cascade tower requires.
-/

open HahnSeries Polynomial PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type} [Field K] [Algebra ℂ K]

/-- The top symbol `Q(u,·)` of a first-order relation, at the value `u` of the first coordinate. -/
def topSymbolAt (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ) (u : K) : K[X] :=
  ∑ i ∈ firstOrderTopNewtonFace S A d, Polynomial.C (Polynomial.aeval u (A i)) * Polynomial.X ^ i.2

/-- The relation compactified at `V = ∞`: `t^d P(u, t^(-1), t^(-1) Y)` over `K[[t]]`. -/
def relationCompactAt (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ) (u : K) :
    (PowerSeries K)[X] :=
  ∑ i ∈ S, Polynomial.C (PowerSeries.C (Polynomial.aeval u (A i)) *
    (PowerSeries.X : PowerSeries K) ^ (d - (i.1 + i.2))) * Polynomial.X ^ i.2

/-- The special fibre of the compactified relation is the top symbol. -/
theorem specialFiber_relationCompactAt (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (u : K) (hdegree : ∀ i ∈ S, i.1 + i.2 ≤ d) (hne : ∀ i ∈ S, A i ≠ 0) :
    (relationCompactAt S A d u).map (PowerSeries.constantCoeff (R := K)) =
      topSymbolAt S A d u := by
  classical
  rw [relationCompactAt, topSymbolAt, Polynomial.map_sum, firstOrderTopNewtonFace,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases htop : i.1 + i.2 = d
  · rw [if_pos ⟨htop, hne i hi⟩]
    simp [htop]
  · rw [if_neg (fun h => htop h.1)]
    have hpos : 0 < d - (i.1 + i.2) :=
      Nat.sub_pos_of_lt (lt_of_le_of_ne (hdegree i hi) htop)
    simp [Polynomial.map_mul, Polynomial.map_C, Nat.ne_of_gt hpos]

omit [Algebra ℂ K] in
theorem laurent_single_one_pow (e : ℤ) (n : ℕ) :
    (HahnSeries.single e (1 : K)) ^ n = HahnSeries.single ((n : ℤ) * e) 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, HahnSeries.single_mul_single]
      congr 1
      · push_cast
        ring_nf
      · simp

omit [Algebra ℂ K] in
theorem ofPowerSeries_expand_C_mul_X_pow (R e : ℕ) (hR : R ≠ 0) (c : K) :
    HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.expand R hR (PowerSeries.C c * (PowerSeries.X : PowerSeries K) ^ e)) =
      HahnSeries.single ((R * e : ℕ) : ℤ) c := by
  rw [map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X, map_mul,
    HahnSeries.ofPowerSeries_C, map_pow, map_pow, HahnSeries.ofPowerSeries_X, ← pow_mul]
  induction R * e with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, HahnSeries.single_mul_single]
      simp

omit [Algebra ℂ K] in
theorem relation_laurent_term_identity (R d j k : ℕ) (hR : R ≠ 0) (c : K)
    (z : PowerSeries K) (hdegree : j + k ≤ d) :
    HahnSeries.single ((R * d : ℕ) : ℤ) (1 : K) *
        (HahnSeries.C c * HahnSeries.single (-((R : ℕ) : ℤ)) (1 : K) ^ j *
          (HahnSeries.single (-((R : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K z) ^ k) =
      HahnSeries.ofPowerSeries ℤ K
          (PowerSeries.expand R hR
            (PowerSeries.C c * (PowerSeries.X : PowerSeries K) ^ (d - (j + k)))) *
        (HahnSeries.ofPowerSeries ℤ K z) ^ k := by
  rw [ofPowerSeries_expand_C_mul_X_pow, laurent_single_one_pow, mul_pow,
    laurent_single_one_pow, HahnSeries.C_apply]
  have hsingle :
      HahnSeries.single ((R * d : ℕ) : ℤ) (1 : K) * HahnSeries.single (0 : ℤ) c *
          HahnSeries.single ((j : ℤ) * -((R : ℕ) : ℤ)) (1 : K) *
          HahnSeries.single ((k : ℤ) * -((R : ℕ) : ℤ)) 1 =
        HahnSeries.single ((R * (d - (j + k)) : ℕ) : ℤ) c := by
    rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single,
      HahnSeries.single_mul_single]
    simp only [one_mul, mul_one]
    apply congrArg (fun e : ℤ => HahnSeries.single e c)
    push_cast
    rw [Nat.cast_sub hdegree]
    push_cast
    ring
  rw [← hsingle]
  ring

/-- Evaluation of the relation at `(u, V, W)` in `K((t))`. -/
theorem eval₂_firstOrderMvPoly_laurent (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ)
    (u : K) (V W : LaurentSeries K) :
    MvPolynomial.eval₂ (algebraMap ℂ (LaurentSeries K))
        (fun j : Fin 3 => ![HahnSeries.C u, V, W] j) (firstOrderMvPoly S A) =
      ∑ i ∈ S, HahnSeries.C (Polynomial.aeval u (A i)) * V ^ i.1 * W ^ i.2 := by
  rw [eval₂_firstOrderMvPoly]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range,
    map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_mul, map_pow, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C]

/-- The clearing identity: `t^(Rd) P(u, t^(-R), t^(-R) z) = (expanded compact relation)(z)`. -/
theorem relation_laurent_mul_eq_compactEval (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ)
    (d R : ℕ) (hR : R ≠ 0) (u : K) (z : PowerSeries K)
    (hdegree : ∀ i ∈ S, i.1 + i.2 ≤ d) :
    HahnSeries.single ((R * d : ℕ) : ℤ) (1 : K) *
        (∑ i ∈ S, HahnSeries.C (Polynomial.aeval u (A i)) *
          HahnSeries.single (-((R : ℕ) : ℤ)) (1 : K) ^ i.1 *
          (HahnSeries.single (-((R : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K z) ^ i.2) =
      HahnSeries.ofPowerSeries ℤ K
        (((relationCompactAt S A d u).map
          (PowerSeries.expand (R := K) R hR).toRingHom).eval z) := by
  classical
  rw [Finset.mul_sum, relationCompactAt, Polynomial.map_sum, Polynomial.eval_finsetSum,
    map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    map_mul, map_pow]
  exact relation_laurent_term_identity R d i.1 i.2 hR _ z (hdegree i hi)

/-- **Slope-one Laurent branch with a prescribed top-symbol root.**  Over any algebraically closed
field of characteristic zero, every root `σ` of a nonzero top symbol `Q(u,·)` is the leading
coefficient of a Laurent root `W = t^(-R) z(t)` of `P(u, t^(-R), W)`. -/
theorem exists_relation_laurent_branch [IsAlgClosed K] [CharZero K]
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (hdegree : ∀ i ∈ S, i.1 + i.2 ≤ d) (hne : ∀ i ∈ S, A i ≠ 0)
    (u σ : K) (hQ : topSymbolAt S A d u ≠ 0) (hσ : (topSymbolAt S A d u).IsRoot σ) :
    ∃ (R : ℕ) (_hR : R ≠ 0) (z : PowerSeries K),
      PowerSeries.constantCoeff z = σ ∧
      MvPolynomial.eval₂ (algebraMap ℂ (LaurentSeries K))
        (fun j : Fin 3 => ![HahnSeries.C u, HahnSeries.single (-((R : ℕ) : ℤ)) (1 : K),
          HahnSeries.single (-((R : ℕ) : ℤ)) (1 : K) * HahnSeries.ofPowerSeries ℤ K z] j)
        (firstOrderMvPoly S A) = 0 := by
  let F := relationCompactAt S A d u
  have hfib : (newtonTransform F 0 1 one_ne_zero).map
      (PowerSeries.constantCoeff (R := K)) = topSymbolAt S A d u := by
    rw [newtonTransform_zero_one]
    exact specialFiber_relationCompactAt S A d u hdegree hne
  have hdvd : ∀ i ≤ F.natDegree,
      (PowerSeries.X : PowerSeries K) ^ (0 * (F.natDegree - i)) ∣
        PowerSeries.expand 1 one_ne_zero (F.coeff i) := by
    intro i _
    simp
  obtain ⟨R, hR, z, hz, hzlead⟩ :=
    exists_isRoot_map_expand_with_prescribed_newton_lead_of_specialFiber_ne
      (K := K) 0 1 one_ne_zero hdvd σ (by rw [hfib]; exact hQ) (by rw [hfib]; exact hσ)
  have hzroot : (F.map (PowerSeries.expand (R := K) R hR).toRingHom).IsRoot z := by
    simpa only [Nat.mul_one, Nat.mul_zero, pow_zero, one_mul] using hz
  refine ⟨R, hR, z, hzlead, ?_⟩
  rw [eval₂_firstOrderMvPoly_laurent]
  have hprod := relation_laurent_mul_eq_compactEval S A d R hR u z hdegree
  rw [hzroot, map_zero] at hprod
  exact (mul_eq_zero.mp hprod).resolve_left (by simp)

end

end GaloisForLFunctions.HTGeometry
