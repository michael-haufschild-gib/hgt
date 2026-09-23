import GaloisForLFunctions.RHTower.Sieve.VinogradovReservoirScale

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovLinnikWeight (k : ℕ) : ℕ :=
  k * (k - 1) / 2

def vinogradovMeanExponent (k r : ℕ) : ℕ :=
  k + (2 * k - 2) * (r - 1)

def VinogradovMeanAdmissible (k r : ℕ) : Prop :=
  ∀ u : ℕ, 1 ≤ u → u < r →
    2 * k * u + vinogradovLinnikWeight k ≤
      vinogradovMeanExponent k u + k * (k - 2)

def vinogradovMeanConstant (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 =>
      vinogradovReservoirSmallThreshold k ^ (2 * k * (r + 1)) +
      k.factorial +
      2 * vinogradovMeanConstant k r *
        (vinogradovReservoirSize k ^ (2 : ℕ) * k.factorial *
            2 ^ (vinogradovMeanExponent k r) *
            vinogradovReservoirPrimePowerConstant k ^ (k - 2) +
          (k * k - k) ^ (2 : ℕ)) + 1

theorem vinogradovMeanExponent_one (k : ℕ) :
    vinogradovMeanExponent k 1 = k := by
  simp [vinogradovMeanExponent]

theorem vinogradovMeanExponent_succ
    {k r : ℕ} (hr : 1 ≤ r) :
    vinogradovMeanExponent k (r + 1) =
      vinogradovMeanExponent k r + (2 * k - 2) := by
  have hre : r = (r - 1) + 1 := by omega
  unfold vinogradovMeanExponent
  rw [show r + 1 - 1 = r by omega]
  calc
    k + (2 * k - 2) * r =
        k + (2 * k - 2) * ((r - 1) + 1) := by rw [← hre]
    _ = k + (2 * k - 2) * (r - 1) + (2 * k - 2) := by
      rw [mul_add]
      omega

theorem vinogradovMeanAdmissible_prev
    {k r : ℕ} (h : VinogradovMeanAdmissible k (r + 1)) :
    VinogradovMeanAdmissible k r := by
  intro u hu hur
  exact h u hu (by omega)

theorem vinogradovMeanAdmissible_last
    {k r : ℕ} (hr : 1 ≤ r) (h : VinogradovMeanAdmissible k (r + 1)) :
    2 * k * r + vinogradovLinnikWeight k ≤
      vinogradovMeanExponent k r + k * (k - 2) :=
  h r hr (by omega)

theorem vinogradovMeanAdmissible_of_budget
    {k r : ℕ} (hk2 : 2 ≤ k)
    (hbudget : 2 * r + vinogradovLinnikWeight k ≤ (k - 1) * (k - 2)) :
    VinogradovMeanAdmissible k r := by
  intro u hu hur
  have hku :
      (vinogradovMeanExponent k u + k * (k - 2)) + 2 * u =
        2 * k * u + (k - 1) * (k - 2) := by
    have hk1 : k - 1 + 1 = k := by omega
    have hk2' : k - 2 + 2 = k := by omega
    have hu' : u - 1 + 1 = u := by omega
    have htwo : 2 * k - 2 = 2 * (k - 1) := by omega
    unfold vinogradovMeanExponent
    rw [htwo]
    nlinarith
  have hubudget : 2 * u + vinogradovLinnikWeight k ≤
      (k - 1) * (k - 2) := by
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_of_lt hur)) _).trans
      hbudget
  have hadd : (2 * k * u + vinogradovLinnikWeight k) + 2 * u ≤
      (vinogradovMeanExponent k u + k * (k - 2)) + 2 * u := by
    calc
      (2 * k * u + vinogradovLinnikWeight k) + 2 * u =
          2 * k * u + (2 * u + vinogradovLinnikWeight k) := by omega
      _ ≤ 2 * k * u + (k - 1) * (k - 2) :=
        Nat.add_le_add_left hubudget _
      _ = (vinogradovMeanExponent k u + k * (k - 2)) + 2 * u := hku.symm
  omega

def vinogradovRouteTOrder (s : ℕ) : ℕ := 100 * s

def vinogradovRouteTMomentSteps (s : ℕ) : ℕ :=
  2500 * s ^ (2 : ℕ) - 200 * s

theorem vinogradovRouteTMomentSteps_pos {s : ℕ} (hs : 1 ≤ s) :
    1 ≤ vinogradovRouteTMomentSteps s := by
  unfold vinogradovRouteTMomentSteps
  apply Nat.le_sub_of_add_le
  nlinarith [sq_nonneg (s - 1)]

theorem vinogradovRouteT_admissible {s : ℕ} (hs : 1 ≤ s) :
    VinogradovMeanAdmissible
      (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) := by
  apply vinogradovMeanAdmissible_of_budget (by
    unfold vinogradovRouteTOrder
    omega)
  have hdiv := Nat.mul_div_le
    ((vinogradovRouteTOrder s) * (vinogradovRouteTOrder s - 1)) 2
  have hhalf : 2 * vinogradovLinnikWeight (vinogradovRouteTOrder s) ≤
      vinogradovRouteTOrder s * (vinogradovRouteTOrder s - 1) := by
    simpa only [vinogradovLinnikWeight] using hdiv
  simp only [vinogradovRouteTOrder, vinogradovRouteTMomentSteps] at hhalf ⊢
  have hsprod : 200 * s ≤ 2500 * s ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (s - 1)]
  have hstep : (2500 * s ^ (2 : ℕ) - 200 * s) + 200 * s = 2500 * s ^ (2 : ℕ) :=
    Nat.sub_add_cancel hsprod
  have hk1 : 100 * s - 1 + 1 = 100 * s := by omega
  have hk2 : 100 * s - 2 + 2 = 100 * s := by omega
  nlinarith

theorem card_vinogradovDiagonalSolution_le_trivial (N b k : ℕ) :
    Fintype.card (VinogradovDiagonalSolution N b k) ≤ N ^ (2 * b) := by
  calc
    Fintype.card (VinogradovDiagonalSolution N b k) ≤
        Fintype.card ((Fin b → Fin N) × (Fin b → Fin N)) :=
      Fintype.card_le_of_embedding ⟨Subtype.val, Subtype.val_injective⟩
    _ = N ^ (2 * b) := by
      rw [Fintype.card_prod]
      simp only [Fintype.card_fun, Fintype.card_fin]
      rw [← pow_add]
      congr 1
      omega

theorem vinogradovMeanConstant_ge_small
    (k r : ℕ) :
    vinogradovReservoirSmallThreshold k ^ (2 * k * (r + 1)) ≤
      vinogradovMeanConstant k (r + 1) := by
  simp only [vinogradovMeanConstant]
  omega

theorem vinogradovMeanConstant_ge_factorial
    (k r : ℕ) : k.factorial ≤ vinogradovMeanConstant k (r + 1) := by
  simp only [vinogradovMeanConstant]
  omega

theorem vinogradovMeanConstant_ge_step
    (k r : ℕ) :
    2 * vinogradovMeanConstant k r *
        (vinogradovReservoirSize k ^ (2 : ℕ) * k.factorial *
            2 ^ (vinogradovMeanExponent k r) *
            vinogradovReservoirPrimePowerConstant k ^ (k - 2) +
          (k * k - k) ^ (2 : ℕ)) ≤
      vinogradovMeanConstant k (r + 1) := by
  simp only [vinogradovMeanConstant]
  omega

theorem vinogradov_small_scale_moment_bound
    {N k r : ℕ} (hN : N ≠ 0)
    (hsmall : N ≤ vinogradovReservoirSmallThreshold k) :
    Fintype.card (VinogradovDiagonalSolution N (k * (r + 1)) k) ≤
      vinogradovMeanConstant k (r + 1) *
        N ^ (vinogradovMeanExponent k (r + 1)) := by
  have htriv := card_vinogradovDiagonalSolution_le_trivial N (k * (r + 1)) k
  have hbase : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  have hexp : vinogradovMeanExponent k (r + 1) ≤ 2 * (k * (r + 1)) := by
    have hcoef : 2 * k - 2 ≤ 2 * k := Nat.sub_le _ _
    calc
      vinogradovMeanExponent k (r + 1) = k + (2 * k - 2) * r := by
        simp [vinogradovMeanExponent]
      _ ≤ k + (2 * k) * r :=
        Nat.add_le_add_left (Nat.mul_le_mul_right r hcoef) k
      _ ≤ 2 * (k * (r + 1)) := by nlinarith
  have hHpos : 0 < vinogradovReservoirSmallThreshold k := by
    apply pow_pos
    apply mul_pos
    · omega
    · exact mul_pos (pow_pos (by omega) _) (by omega)
  calc
    Fintype.card (VinogradovDiagonalSolution N (k * (r + 1)) k) ≤
        N ^ (2 * (k * (r + 1))) := htriv
    _ = N ^ (vinogradovMeanExponent k (r + 1)) *
        N ^ (2 * (k * (r + 1)) - vinogradovMeanExponent k (r + 1)) := by
      rw [← pow_add]
      rw [Nat.add_sub_of_le hexp]
    _ ≤ N ^ (vinogradovMeanExponent k (r + 1)) *
        vinogradovReservoirSmallThreshold k ^
          (2 * (k * (r + 1)) - vinogradovMeanExponent k (r + 1)) := by
      gcongr
    _ ≤ N ^ (vinogradovMeanExponent k (r + 1)) *
        vinogradovReservoirSmallThreshold k ^ (2 * k * (r + 1)) := by
      gcongr
      calc
        2 * (k * (r + 1)) - vinogradovMeanExponent k (r + 1) ≤
            2 * (k * (r + 1)) := Nat.sub_le _ _
        _ = 2 * k * (r + 1) := by ring
    _ ≤ N ^ (vinogradovMeanExponent k (r + 1)) *
        vinogradovMeanConstant k (r + 1) := by
      gcongr
      exact vinogradovMeanConstant_ge_small k r
    _ = vinogradovMeanConstant k (r + 1) *
        N ^ (vinogradovMeanExponent k (r + 1)) := Nat.mul_comm _ _

theorem pow_mul_pow_vinogradov_scale
    {p M N E k C A : ℕ} (hp : 0 < p)
    (hpm : p * M ≤ 2 * N) (hpk : p ^ k ≤ C * N)
    (hA : A ≤ E + k * (k - 2)) :
    p ^ A * M ^ E ≤
      2 ^ E * C ^ (k - 2) * N ^ (E + (k - 2)) := by
  calc
    p ^ A * M ^ E ≤ p ^ (E + k * (k - 2)) * M ^ E :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp hA)
    _ = (p * M) ^ E * (p ^ k) ^ (k - 2) := by
      rw [pow_add, pow_mul, mul_pow]
      ring
    _ ≤ (2 * N) ^ E * (C * N) ^ (k - 2) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hpm E)
        (Nat.pow_le_pow_left hpk (k - 2))
    _ = 2 ^ E * C ^ (k - 2) * N ^ (E + (k - 2)) := by
      simp only [mul_pow, pow_add]
      ring

theorem vinogradov_large_scale_good_term
    {N k r p : ℕ} (hk2 : 2 ≤ k) (hr : 1 ≤ r)
    (hp : p.Prime) (hpm : p * (N ⌈/⌉ p) ≤ 2 * N)
    (hpkscale : p ^ k ≤ vinogradovReservoirPrimePowerConstant k * N)
    (hIH : Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ p) (k * r) k) ≤
      vinogradovMeanConstant k r *
        (N ⌈/⌉ p) ^ (vinogradovMeanExponent k r))
    (hadm : 2 * k * r + vinogradovLinnikWeight k ≤
      vinogradovMeanExponent k r + k * (k - 2)) :
    p ^ (2 * (k * r)) *
        (N ^ k * (k.factorial * p ^ vinogradovLinnikWeight k *
          Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ p) (k * r) k))) ≤
      vinogradovMeanConstant k r *
        (k.factorial * 2 ^ (vinogradovMeanExponent k r) *
          vinogradovReservoirPrimePowerConstant k ^ (k - 2)) *
        N ^ (vinogradovMeanExponent k (r + 1)) := by
  let E := vinogradovMeanExponent k r
  let C := vinogradovReservoirPrimePowerConstant k
  have hA : 2 * (k * r) + vinogradovLinnikWeight k ≤ E + k * (k - 2) := by
    simpa [E, mul_assoc] using hadm
  have hscale := pow_mul_pow_vinogradov_scale hp.pos hpm hpkscale hA
  have hEsucc : vinogradovMeanExponent k (r + 1) = E + (2 * k - 2) :=
    vinogradovMeanExponent_succ hr
  have hexpcombine : k + (E + (k - 2)) = E + (2 * k - 2) := by
    omega
  have hpowcombine : N ^ k * N ^ (E + (k - 2)) =
      N ^ (k + (E + (k - 2))) := (pow_add N k (E + (k - 2))).symm
  calc
    p ^ (2 * (k * r)) *
        (N ^ k * (k.factorial * p ^ vinogradovLinnikWeight k *
          Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ p) (k * r) k))) ≤
        p ^ (2 * (k * r)) *
          (N ^ k * (k.factorial * p ^ vinogradovLinnikWeight k *
            (vinogradovMeanConstant k r * (N ⌈/⌉ p) ^ E))) := by gcongr
    _ = vinogradovMeanConstant k r * k.factorial * N ^ k *
        (p ^ (2 * (k * r) + vinogradovLinnikWeight k) *
          (N ⌈/⌉ p) ^ E) := by
      rw [pow_add]
      ring
    _ ≤ vinogradovMeanConstant k r * k.factorial * N ^ k *
        (2 ^ E * C ^ (k - 2) * N ^ (E + (k - 2))) := by gcongr
    _ = vinogradovMeanConstant k r *
        (k.factorial * 2 ^ E * C ^ (k - 2)) *
        N ^ (vinogradovMeanExponent k (r + 1)) := by
      rw [hEsucc]
      calc
        vinogradovMeanConstant k r * k.factorial * N ^ k *
            (2 ^ E * C ^ (k - 2) * N ^ (E + (k - 2))) =
            (vinogradovMeanConstant k r *
              (k.factorial * 2 ^ E * C ^ (k - 2))) *
              (N ^ k * N ^ (E + (k - 2))) := by ring
        _ = (vinogradovMeanConstant k r *
              (k.factorial * 2 ^ E * C ^ (k - 2))) *
              N ^ (k + (E + (k - 2))) := by
            rw [hpowcombine]
        _ = vinogradovMeanConstant k r *
              (k.factorial * 2 ^ E * C ^ (k - 2)) *
              N ^ (E + (2 * k - 2)) := by
            congr 1
            exact congrArg (N ^ ·) hexpcombine

theorem vinogradov_collision_induction_term
    {N k r : ℕ} (hk2 : 2 ≤ k) (hr : 1 ≤ r)
    (hIH : Fintype.card (VinogradovDiagonalSolution N (k * r) k) ≤
      vinogradovMeanConstant k r * N ^ (vinogradovMeanExponent k r)) :
    ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
        Fintype.card (VinogradovDiagonalSolution N (k * r) k) ≤
      vinogradovMeanConstant k r * (k * k - k) ^ (2 : ℕ) *
        N ^ (vinogradovMeanExponent k (r + 1)) := by
  let E := vinogradovMeanExponent k r
  have hEsucc : vinogradovMeanExponent k (r + 1) = E + (2 * k - 2) :=
    vinogradovMeanExponent_succ hr
  have hexp : 2 * (k - 1) = 2 * k - 2 := by omega
  have hexp' : 2 * (k - 1) + E = E + (2 * k - 2) := by omega
  have hpow : N ^ (2 * (k - 1)) * N ^ E =
      N ^ (E + (2 * k - 2)) := by
    rw [← pow_add, hexp']
  calc
    ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
        Fintype.card (VinogradovDiagonalSolution N (k * r) k) ≤
      ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
        (vinogradovMeanConstant k r * N ^ E) := by gcongr
    _ = vinogradovMeanConstant k r * (k * k - k) ^ (2 : ℕ) *
        (N ^ (2 * (k - 1)) * N ^ E) := by
      rw [mul_pow, ← pow_mul]
      ring
    _ = vinogradovMeanConstant k r * (k * k - k) ^ (2 : ℕ) *
        N ^ (E + (2 * k - 2)) := by
      rw [hpow]
    _ = vinogradovMeanConstant k r * (k * k - k) ^ (2 : ℕ) *
        N ^ (vinogradovMeanExponent k (r + 1)) := by rw [hEsucc]

theorem vinogradov_mean_value_bound
    (k r : ℕ) (hk2 : 2 ≤ k) (hr : 1 ≤ r)
    (hadm : VinogradovMeanAdmissible k r) (N : ℕ) (hN : N ≠ 0) :
    Fintype.card (VinogradovDiagonalSolution N (k * r) k) ≤
      vinogradovMeanConstant k r * N ^ (vinogradovMeanExponent k r) := by
  induction r generalizing N with
  | zero => omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · subst r
        have hdiag := card_vinogradovDiagonalSolution_le
          (N := N) (b := k) (k := k) (le_refl k)
        calc
          Fintype.card (VinogradovDiagonalSolution N (k * 1) k) =
              Fintype.card (VinogradovDiagonalSolution N k k) := by simp
          _ ≤ k.factorial * N ^ k := hdiag
          _ ≤ vinogradovMeanConstant k 1 * N ^ k := by
            gcongr
            exact vinogradovMeanConstant_ge_factorial k 0
          _ = vinogradovMeanConstant k 1 *
              N ^ (vinogradovMeanExponent k 1) := by
            rw [vinogradovMeanExponent_one]
      · have hrpos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
        have hprevAdm : VinogradovMeanAdmissible k r :=
          vinogradovMeanAdmissible_prev hadm
        have hlast := vinogradovMeanAdmissible_last hrpos hadm
        by_cases hsmall : N ≤ vinogradovReservoirSmallThreshold k
        · exact vinogradov_small_scale_moment_bound hN hsmall
        · have hBN : vinogradovReservoirBound N k ≤ N := by
            by_contra hnot
            have hfail : N < vinogradovReservoirBound N k :=
              Nat.lt_of_not_ge hnot
            exact hsmall (vinogradovReservoirBound_failure_small hk2 hN hfail)
          have hrec := vinogradov_moment_bertrand_recurrence
            (N := N) (k := k) (b := k * r)
            (by omega : k ≠ 0) (mul_ne_zero (by omega) hr0) hN
          let R := vinogradovReservoirSize k
          let D := vinogradovMeanConstant k r
          let E := vinogradovMeanExponent k r
          let C := vinogradovReservoirPrimePowerConstant k
          let W := k.factorial * 2 ^ E * C ^ (k - 2)
          let X := N ^ (vinogradovMeanExponent k (r + 1))
          have hgoodEach : ∀ i : Fin R,
              (vinogradovReservoirPrime N k i) ^ (2 * (k * r)) *
                (N ^ k * (k.factorial *
                  (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
                  Fintype.card (VinogradovDiagonalSolution
                    (N ⌈/⌉ (vinogradovReservoirPrime N k i)) (k * r) k))) ≤
                D * W * X := by
            intro i
            let p := vinogradovReservoirPrime N k i
            have hp := vinogradovReservoirPrime_prime (N := N) (k := k) i
            have hM := ceilDiv_ne_zero_of_ne_zero hN hp.pos
            have hIH := ih hrpos hprevAdm (N ⌈/⌉ p) hM
            have hpm := vinogradovReservoirPrime_mul_ceilDiv_le_two_mul
              hN i hBN
            have hpkscale := vinogradovReservoirPrime_pow_le_scale
              (by omega : k ≠ 0) hN i
            simpa [p, D, E, C, W, X, vinogradovLinnikWeight] using
              vinogradov_large_scale_good_term hk2 hrpos hp hpm hpkscale hIH hlast
          have hsum :
              (∑ i : Fin R,
                (vinogradovReservoirPrime N k i) ^ (2 * (k * r)) *
                  (N ^ k * (k.factorial *
                    (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
                    Fintype.card (VinogradovDiagonalSolution
                      (N ⌈/⌉ (vinogradovReservoirPrime N k i)) (k * r) k)))) ≤
                R * (D * W * X) := by
            calc
              _ ≤ ∑ _i : Fin R, D * W * X := by
                exact Finset.sum_le_sum fun i _ => hgoodEach i
              _ = R * (D * W * X) := by simp [R]
          have hgood : R *
              (∑ i : Fin R,
                (vinogradovReservoirPrime N k i) ^ (2 * (k * r)) *
                  (N ^ k * (k.factorial *
                    (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
                    Fintype.card (VinogradovDiagonalSolution
                      (N ⌈/⌉ (vinogradovReservoirPrime N k i)) (k * r) k)))) ≤
                D * (R ^ (2 : ℕ) * W) * X := by
            calc
              _ ≤ R * (R * (D * W * X)) := Nat.mul_le_mul_left R hsum
              _ = D * (R ^ (2 : ℕ) * W) * X := by ring
          have hIHN := ih hrpos hprevAdm N hN
          have hbad : ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
              Fintype.card (VinogradovDiagonalSolution N (k * r) k) ≤
              D * (k * k - k) ^ (2 : ℕ) * X := by
            simpa [D, X] using
              vinogradov_collision_induction_term hk2 hrpos hIHN
          have hcoeff :
              2 * D * (R ^ (2 : ℕ) * W + (k * k - k) ^ (2 : ℕ)) ≤
                vinogradovMeanConstant k (r + 1) := by
            simpa only [D, R, W, E, C, mul_assoc] using
              vinogradovMeanConstant_ge_step k r
          have hRHS :
              2 * (R *
                  (∑ i : Fin R,
                    (vinogradovReservoirPrime N k i) ^ (2 * (k * r)) *
                      (N ^ k * (k.factorial *
                        (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
                        Fintype.card (VinogradovDiagonalSolution
                          (N ⌈/⌉ (vinogradovReservoirPrime N k i)) (k * r) k)))) +
                ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
                  Fintype.card (VinogradovDiagonalSolution N (k * r) k)) ≤
                vinogradovMeanConstant k (r + 1) * X := by
            calc
              _ ≤ 2 * (D * (R ^ (2 : ℕ) * W) * X +
                    D * (k * k - k) ^ (2 : ℕ) * X) := by gcongr
              _ = (2 * D * (R ^ (2 : ℕ) * W + (k * k - k) ^ (2 : ℕ))) * X := by ring
              _ ≤ vinogradovMeanConstant k (r + 1) * X :=
                Nat.mul_le_mul_right X hcoeff
          have hrec' :
              Fintype.card (VinogradovDiagonalSolution N (k * (r + 1)) k) ≤
                2 * (R *
                    (∑ i : Fin R,
                      (vinogradovReservoirPrime N k i) ^ (2 * (k * r)) *
                        (N ^ k * (k.factorial *
                          (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
                          Fintype.card (VinogradovDiagonalSolution
                            (N ⌈/⌉ (vinogradovReservoirPrime N k i)) (k * r) k)))) +
                  ((k * k - k) * N ^ (k - 1)) ^ (2 : ℕ) *
                    Fintype.card (VinogradovDiagonalSolution N (k * r) k)) := by
            rw [show k * (r + 1) = k + k * r by ring]
            simpa only [R] using hrec
          exact hrec'.trans (by simpa [X] using hRHS)

theorem vinogradovRouteT_meanExponent_exact
    {s : ℕ} (hs : 1 ≤ s) :
    vinogradovMeanExponent
        (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) =
      2 * vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s -
          vinogradovRouteTOrder s * (vinogradovRouteTOrder s + 1) / 2 +
        (350 * s + 2) := by
  have hr := vinogradovRouteTMomentSteps_pos hs
  have hsprod : 200 * s ≤ 2500 * s ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (s - 1)]
  have hrval : (2500 * s ^ (2 : ℕ) - 200 * s) + 200 * s = 2500 * s ^ (2 : ℕ) :=
    Nat.sub_add_cancel hsprod
  have hdiv : (100 * s) * (100 * s + 1) / 2 =
      5000 * s ^ (2 : ℕ) + 50 * s := by
    calc
      (100 * s) * (100 * s + 1) / 2 =
          2 * (50 * s * (100 * s + 1)) / 2 := by
            congr 1
            ring
      _ = 50 * s * (100 * s + 1) := Nat.mul_div_cancel_left _ (by omega)
      _ = 5000 * s ^ (2 : ℕ) + 50 * s := by ring
  have hsub : (100 * s) * (100 * s + 1) / 2 ≤
      2 * (100 * s) * (2500 * s ^ (2 : ℕ) - 200 * s) := by
    rw [hdiv]
    nlinarith
  unfold vinogradovMeanExponent vinogradovRouteTOrder
    vinogradovRouteTMomentSteps
  rw [hdiv]
  have hrsub : 2500 * s ^ (2 : ℕ) - 200 * s - 1 + 1 =
      2500 * s ^ (2 : ℕ) - 200 * s := Nat.sub_add_cancel hr
  have hkcoef : 2 * (100 * s) - 2 + 2 = 2 * (100 * s) := by omega
  have hsum :
      (100 * s + (2 * (100 * s) - 2) *
          (2500 * s ^ (2 : ℕ) - 200 * s - 1)) +
          (5000 * s ^ (2 : ℕ) + 50 * s) =
        2 * (100 * s) * (2500 * s ^ (2 : ℕ) - 200 * s) +
          (350 * s + 2) := by
    nlinarith
  omega

theorem vinogradovRouteT_mean_value_bound
    {s N : ℕ} (hs : 1 ≤ s) (hN : N ≠ 0) :
    Fintype.card (VinogradovDiagonalSolution N
        (vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s)
        (vinogradovRouteTOrder s)) ≤
      vinogradovMeanConstant
          (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) *
        N ^ (2 * vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s -
            vinogradovRouteTOrder s * (vinogradovRouteTOrder s + 1) / 2 +
          (350 * s + 2)) := by
  rw [← vinogradovRouteT_meanExponent_exact hs]
  exact vinogradov_mean_value_bound
    (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s)
    (by unfold vinogradovRouteTOrder; omega)
    (vinogradovRouteTMomentSteps_pos hs)
    (vinogradovRouteT_admissible hs) N hN

end

end RHTower.Sieve
