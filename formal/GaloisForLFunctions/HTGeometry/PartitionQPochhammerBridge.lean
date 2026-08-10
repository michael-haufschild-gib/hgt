import GaloisForLFunctions.HTGeometry.PartitionGeneratingFunction
import GaloisForLFunctions.HTGeometry.QBinomialTheorem

/-!
# Euler's identity in q-Pochhammer form

The generating function of the partitions with exactly `n` parts, transported from `ℝ≥0∞` to `ℝ`,
is the local q-geometric coefficient `qⁿ/(q;q)ₙ` of the corpus's q-Pochhammer layer.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ENNReal

noncomputable section

/-- The real generating function of the partitions with exactly `n` parts. -/
def exactGFReal (q : RealEulerNome) (n : ℕ) : ℝ :=
  (exactGF (ENNReal.ofReal q.val) n).toReal

theorem ofReal_nome_lt_one (q : RealEulerNome) : ENNReal.ofReal q.val < 1 := by
  calc ENNReal.ofReal q.val < ENNReal.ofReal 1 :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr q.lt_one
    _ = 1 := ENNReal.ofReal_one

theorem exactGF_ne_top (q : ℝ≥0∞) (hq : q < 1) (n : ℕ) : exactGF q n ≠ ⊤ := by
  rw [exactGF_eq_mul]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hq.ne_top) (atMostGF_ne_top q hq n)

theorem prod_ofReal_eq (q : RealEulerNome) (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 - (ENNReal.ofReal q.val) ^ (i + 1)))
      = ENNReal.ofReal (realQFactorial q n) := by
  rw [realQFactorial, ENNReal.ofReal_prod_of_nonneg]
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hle : q.val ^ (i + 1) ≤ 1 := pow_le_one₀ q.pos.le q.lt_one.le
    rw [ENNReal.ofReal_sub _ (pow_nonneg q.pos.le _), ENNReal.ofReal_one,
      ENNReal.ofReal_pow q.pos.le]
  · intro i _
    have hle : q.val ^ (i + 1) ≤ 1 := pow_le_one₀ q.pos.le q.lt_one.le
    linarith

/-- **Euler's identity.**  The partitions with exactly `n` parts have generating function
`qⁿ/(q;q)ₙ`. -/
theorem exactGFReal_eq_qGeometricCoefficient (q : RealEulerNome) (n : ℕ) :
    exactGFReal q n = qGeometricCoefficient q n := by
  have hq := ofReal_nome_lt_one q
  have hmain := exactGF_mul_prod (ENNReal.ofReal q.val) hq n
  rw [prod_ofReal_eq q n] at hmain
  have hne : exactGF (ENNReal.ofReal q.val) n ≠ ⊤ := exactGF_ne_top _ hq n
  have hFpos : 0 < realQFactorial q n := realQFactorial_pos q n
  have htoReal := congrArg ENNReal.toReal hmain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hFpos.le, ← ENNReal.ofReal_pow q.pos.le,
    ENNReal.toReal_ofReal (pow_nonneg q.pos.le n)] at htoReal
  rw [exactGFReal, qGeometricCoefficient, eq_div_iff hFpos.ne']
  exact htoReal

/-! ## The local socle mass -/

/-- The `p`-local mass of the configurations with exactly `n` cyclic factors: the infinite
q-Pochhammer normalisation times the exact-part generating function. -/
def localSocleMass (q : RealEulerNome) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (realQFactorialInf q) * exactGF (ENNReal.ofReal q.val) n

theorem localSocleMass_ne_top (q : RealEulerNome) (n : ℕ) : localSocleMass q n ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (exactGF_ne_top _ (ofReal_nome_lt_one q) n)

/-- **(GAS.5), local form.**  The `p`-local mass of the configurations with exactly `n` cyclic
factors is the Euler weight `w_{q,n} = (q;q)_∞ · qⁿ/(q;q)_n`. -/
theorem localSocleMass_toReal (q : RealEulerNome) (n : ℕ) :
    (localSocleMass q n).toReal = realQFactorialInf q * qGeometricCoefficient q n := by
  rw [localSocleMass, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (realQFactorialInf_pos q).le]
  congr 1
  exact exactGFReal_eq_qGeometricCoefficient q n

theorem localSocleMass_eq_ofReal (q : RealEulerNome) (n : ℕ) :
    localSocleMass q n
      = ENNReal.ofReal (realQFactorialInf q * qGeometricCoefficient q n) := by
  rw [← localSocleMass_toReal q n, ENNReal.ofReal_toReal (localSocleMass_ne_top q n)]

/-! ## The mass of a single local configuration -/

theorem tprod_occupation_pow (q : RealEulerNome) (g : PartConfig) :
    (∏' j : ℕ, (q.val ^ (j + 1)) ^ (g j)) = q.val ^ partSize g := by
  classical
  have hzero : ∀ j ∉ g.support, (q.val ^ (j + 1)) ^ (g j) = 1 := by
    intro j hj
    rw [Finsupp.notMem_support_iff.mp hj, pow_zero]
  rw [tprod_eq_prod hzero, partSize, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← pow_mul]

theorem multipliable_occupation_pow (q : RealEulerNome) (g : PartConfig) :
    Multipliable (fun j : ℕ => (q.val ^ (j + 1)) ^ (g j)) := by
  classical
  refine multipliable_of_ne_finset_one (s := g.support) fun j hj => ?_
  rw [Finsupp.notMem_support_iff.mp hj, pow_zero]

/-- **The mass of one local configuration.**  Under the product of the geometric depth modes with
ratio `q^{j+1}`, a configuration with occupation numbers `g` has mass `(q;q)_∞ · q^{size g}`. -/
theorem tprod_localModeMass (q : RealEulerNome) (g : PartConfig) :
    (∏' j : ℕ, ((q.val ^ (j + 1)) ^ (g j) * (1 - q.val ^ (j + 1))))
      = realQFactorialInf q * q.val ^ partSize g := by
  rw [(multipliable_occupation_pow q g).tprod_mul (realQFactorial_multipliable q),
    tprod_occupation_pow, realQFactorialInf, mul_comm]

/-- **(GAS.5), local marginal.**  Summing the local configuration masses over the configurations
with exactly `n` cyclic factors gives the local socle mass. -/
theorem tsum_localModeMass_eq_localSocleMass (q : RealEulerNome) (n : ℕ) :
    (∑' g : {g : PartConfig // partCount g = n},
        ENNReal.ofReal (∏' j : ℕ, ((q.val ^ (j + 1)) ^ (g.1 j) * (1 - q.val ^ (j + 1)))))
      = localSocleMass q n := by
  have hterm : ∀ g : {g : PartConfig // partCount g = n},
      ENNReal.ofReal (∏' j : ℕ, ((q.val ^ (j + 1)) ^ (g.1 j) * (1 - q.val ^ (j + 1))))
        = ENNReal.ofReal (realQFactorialInf q) * ENNReal.ofReal q.val ^ partSize g.1 := by
    intro g
    rw [tprod_localModeMass q g.1, ENNReal.ofReal_mul (realQFactorialInf_pos q).le,
      ENNReal.ofReal_pow q.pos.le]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, localSocleMass, exactGF]

/-- **(GAS.5), local form, real value.**  The local socle marginal is the Euler weight. -/
theorem tsum_localModeMass_toReal (q : RealEulerNome) (n : ℕ) :
    (∑' g : {g : PartConfig // partCount g = n},
        ENNReal.ofReal (∏' j : ℕ, ((q.val ^ (j + 1)) ^ (g.1 j) * (1 - q.val ^ (j + 1))))).toReal
      = realQFactorialInf q * qGeometricCoefficient q n := by
  rw [tsum_localModeMass_eq_localSocleMass q n, localSocleMass_toReal q n]

end

end GaloisForLFunctions.HTGeometry
