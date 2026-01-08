// this is a Web Worker

// Linear algebra over finite field F_2
const BitMatrix = class extends Uint8Array {
  constructor (rows, cols) {
    rows |= 0;
    cols |= 0;
    if (rows < 0 || cols < 0) {
      throw new TypeError ('invalid size');
    }

    super (rows * cols);

    Reflect.defineProperty (this, 'rows', {value: rows});
    Reflect.defineProperty (this, 'cols', {value: cols});
  }

  static get [Symbol.species] () {
    return Uint8Array;
  }

  get size () {
    return new Uint32Array ([this.rows, this.cols]);
  }

  toIndex (i, j) {
    if (i < 0) i = (i % this.rows) + this.rows;
    i %= this.rows;
    if (j < 0) j = (j % this.cols) + this.cols;
    j %= this.cols;
    return i * this.cols + j;
  }

  get (i, j) {
    return this[this.toIndex (i, j)] & 1;
  }

  getRow (i) {
    if (i < 0) i = (i % this.rows) + this.rows;
    i %= this.rows;
    const start = i * this.cols;
    return this.subarray (start, start + this.cols);
  }

  getColumn (j) {
    if (j < 0) j = (j % this.cols) + this.cols;
    j %= this.cols;
    const matrix = this;
    return new Uint8Array (function * () {
      for (let i = 0; i < matrix.rows; i++) {
        yield matrix[i * matrix.cols + j];
      }
    } ());
  }

  add (i, j, bit) {
    return this[this.toIndex (i, j)] ^= bit & 1;
  }

  flip (i, j) {
    return this[this.toIndex (i, j)] ^= 1;
  }

  set (i, j, bit) {
    return this[this.toIndex (i, j)] = bit & 1;
  }

  multiply (i, j, bit) {
    return this[this.toIndex (i, j)] &= bit & 1;
  }

  nullify (i, j) {
    return this[this.toIndex (i, j)] &= 0;
  }

  clear () {
    if (!super.fill) {
      Array.prototype.fill.call (this, 0);
    } else {
      super.fill (0);
    }
    return this;
  }

  fill (bit) {
    if (!super.fill) {
      Array.prototype.fill.call (this, bit & 1);
    } else {
      super.fill (bit & 1);
    }
    return this;
  }

  fillRow (bit, i) {
    if (i < 0) i = (i % this.rows) + this.rows;
    i %= this.rows;
    const start = i * this.cols;
    if (!super.fill) {
      Array.prototype.fill.call (this, bit & 1, start, start + this.cols);
    } else {
      super.fill (bit & 1, start, start + this.cols);
    }
    return this;
  }

  fillColumn (bit, j) {
    if (j < 0) j = (j % this.cols) + this.cols;
    j %= this.cols;
    bit &= 1;
    for (let i = 0; i < this.rows; i++) {
      this[i * this.cols + j] = bit;
    }
    return this;
  }

  swapRows (i1, i2) {
    if (i1 < 0) i1 = (i1 % this.rows) + this.rows;
    i1 %= this.rows;
    if (i2 < 0) i2 = (i2 % this.rows) + this.rows;
    i2 %= this.rows;
    const start1 = i1 * this.cols;
    const start2 = i2 * this.cols;
    const row1 = new Uint8Array (this.subarray (start1, start1 + this.cols));
    const row2 = new Uint8Array (this.subarray (start2, start2 + this.cols));
    super.set (row1, start2);
    super.set (row2, start1);
    return this;
  }

  addRows (to, from) {
    if (to < 0) to = (to % this.rows) + this.rows;
    to %= this.rows;
    if (from < 0) from = (from % this.rows) + this.rows;
    from %= this.rows;
    const to_start = to * this.cols;
    const from_start = from * this.cols;
    for (let j = 0; j < this.cols; j++) {
      this[to_start + j] ^= this[from_start + j];
    }
    return this;
  }

  // Gaussian elimination
  rowReduction () {
    this.rank = 0;
    for (let row = 0; row < this.rows; row++) {
      for (let j = row; j < this.cols; j++) {
        let i;
        for (i = row; i < this.rows; i++) {
          if (this[i * this.cols + j]) {
            this.rank++;
            break;
          }
        }

        if (i == this.rows) {
          continue;
        } else if (i > row) {
          this.swapRows (i, row);
        }

        for (i = 0; i < this.rows; i++) {
          if (i == row) continue;
          if (this[i * this.cols + j]) {
            this.addRows (i, row);
          }
        }

        break;
      }
    }

    return this.rank;
  }

  getKernel () {
    this.rowReduction ();
    let column = 0;
    const basis = [];
    const pivots = [];

    for (let row = 0; row < this.rows; row++) {
      while (column < this.cols && 0 == this[row * this.cols + column]) {
        const vector = new Uint8Array (this.cols);
        for (let i = 0; i < row; i++) {
          const pivot = pivots[i];
          vector[pivot] = this[i * this.cols + column];
        }
        vector[column] = 1;
        basis.push (vector);
        column++;
      }

      if (column < this.cols) {
        pivots[row] = column;
        column++;
        continue;
      } else {
        break;
      }
    }

    return basis;
  }

  toString () {
    let str = '';
    for (let i = 0; i < this.rows; i++) {
      str += '[' + this.getRow (i) + ']\n';
    }
    return str;
  }
};

function abs(a) {
  return a < 0n ? -a : a;
}

function gcd (a, b) {
  let aAbs = abs(a);
  let bAbs = abs(b);

  if (aAbs === 0n) {
    return bAbs;
  } else if (bAbs === 0n) {
    return aAbs;
  }

  let shift = 0n;
  while (((aAbs | bAbs) & 1n) === 0n) {
    aAbs >>= 1n;
    bAbs >>= 1n;
    shift++;
  }
  while ((aAbs & 1n) === 0n) aAbs >>= 1n;
  do {
    while ((bAbs & 1n) === 0n) bAbs >>= 1n;
    if (aAbs > bAbs) {
      const x = aAbs;
      aAbs = bAbs;
      bAbs = x;
    }
    bAbs -= aAbs;
  } while (bAbs !== 0n);

  return aAbs << shift;
}

function eGcd(a, b) {
  if (a <= 0n || b <= 0n) throw new RangeError('Negative');

  let x = 0n;
  let y = 1n;
  let u = 1n;
  let v = 0n;

  while (a !== 0n) {
    const q = b / a;
    const r = b % a;
    const m = x - (u * q);
    const n = y - (v * q);
    b = a;
    a = r;
    x = u;
    y = v;
    u = m;
    v = n;
  }
  return {
    g: b,
    x,
    y
  };
}

function toZn(a, n) {
  if (n <= 0n) {
    throw new RangeError('n must be positive');
  }
  const aZn = a % n;
  return (aZn < 0n) ? aZn + n : aZn;
}

function modInv(a, n) {
  const egcd = eGcd(toZn(a, n), n);
  if (egcd.g !== 1n) {
    throw new RangeError(`${a.toString()} does not have inverse modulo ${n.toString()}`);
  } else {
    return toZn(egcd.x, n);
  }
}

function modPow(b, e, n) {
  if (n <= 0n) {
    throw new RangeError('n must be positive');
  } else if (n === 1n) {
    return 0n;
  }

  b = toZn(b, n);

  if (e < 0n) {
    return modInv(modPow(b, abs(e), n), n);
  }

  let r = 1n;
  while (e > 0) {
    if ((e % 2n) === 1n) {
      r = r * b % n;
    }
    e = e / 2n;
    b = b ** 2n % n;
  }
  return r;
}

// Euler's criterion
const isQuadraticResidue = (n, p) => {
  if (p <= 2n) {
    return true;
  }

  const e = p >> 1n;
  const result = modPow(n, e, p);
  return result === 1n;
};

// Tonelli--Shanks algorithm
const modular_sqrt = (n, p, l) => {
  if (p <= 2n) {
    return n % p;
  }

  let q = p - 1n;
  let s = 0n;
  while (0n == (1n & q)) {
    s++;
    q >>= 1n;
  }

  let z = 2n;
  while (isQuadraticResidue(z, p)) {
    z++;
  }

  let m = s;
  let c = modPow(z, q, p);
  let t = modPow(n, q, p);
  let q_div_2 = (q + 1n) >> 1n;
  let r = modPow(n, q_div_2, p);

  while (true) {
    if (t == 0n) {
      return t;
    } else if (t == 1n) {
      return r;
    }

    let i = 1n;
    let e = 1n;
    while (i < m) {
      e = e * 2n;
      if (modPow(t, e, p) == 1n) {
        break;
      }
      i++;
    }
    if (i == m) {
      throw new TypeError ('no root');
    }

    let b = modPow(c, (2n ** (m - i - 1n)), p);
    m = i;
    c = modPow(b, 2n, p);
    t = (t * c) % p;
    r = (r * b) % p;
  }
};

// binary search using integer arithmetic
const ceil_sqrt = n => {
  let hi = 1n;
  while (hi * hi <= n) {
    hi = hi * 2n;
  }

  let lo = hi / 2n;

  let result;
  while (lo <= hi) {
    let mid = (lo + hi) / 2n;
    let sq = mid * mid;
    if (sq == n) {
      return mid;
    } else if (sq > n) {
      result = mid;
      hi = mid - 1n;
    } else {
      lo = mid + 1n;
    }
  }

  return result;
};

// test if a JavaScript number is a prime
const isPrime_deterministic = n => {
  if (n < 2) {
    return false;
  } else if (n < 4) {
    return true;
  } else if (n % 2 == 0) {
    return false;
  }

  let d = 3;
  while (d * d <= n) {
    if (n % d == 0) {
      return false;
    }
    d += 2;
  }

  return true;
};

// primes < 10000
const smallPrimes = [
  2,
  3,
  5,
  7,
  11,
  13,
  17,
  19,
  23,
  29,
  31,
  37,
  41,
  43,
  47,
  53,
  59,
  61,
  67,
  71,
  73,
  79,
  83,
  89,
  97,
  101,
  103,
  107,
  109,
  113,
  127,
  131,
  137,
  139,
  149,
  151,
  157,
  163,
  167,
  173,
  179,
  181,
  191,
  193,
  197,
  199,
  211,
  223,
  227,
  229,
  233,
  239,
  241,
  251,
  257,
  263,
  269,
  271,
  277,
  281,
  283,
  293,
  307,
  311,
  313,
  317,
  331,
  337,
  347,
  349,
  353,
  359,
  367,
  373,
  379,
  383,
  389,
  397,
  401,
  409,
  419,
  421,
  431,
  433,
  439,
  443,
  449,
  457,
  461,
  463,
  467,
  479,
  487,
  491,
  499,
  503,
  509,
  521,
  523,
  541,
  547,
  557,
  563,
  569,
  571,
  577,
  587,
  593,
  599,
  601,
  607,
  613,
  617,
  619,
  631,
  641,
  643,
  647,
  653,
  659,
  661,
  673,
  677,
  683,
  691,
  701,
  709,
  719,
  727,
  733,
  739,
  743,
  751,
  757,
  761,
  769,
  773,
  787,
  797,
  809,
  811,
  821,
  823,
  827,
  829,
  839,
  853,
  857,
  859,
  863,
  877,
  881,
  883,
  887,
  907,
  911,
  919,
  929,
  937,
  941,
  947,
  953,
  967,
  971,
  977,
  983,
  991,
  997,
  1009,
  1013,
  1019,
  1021,
  1031,
  1033,
  1039,
  1049,
  1051,
  1061,
  1063,
  1069,
  1087,
  1091,
  1093,
  1097,
  1103,
  1109,
  1117,
  1123,
  1129,
  1151,
  1153,
  1163,
  1171,
  1181,
  1187,
  1193,
  1201,
  1213,
  1217,
  1223,
  1229,
  1231,
  1237,
  1249,
  1259,
  1277,
  1279,
  1283,
  1289,
  1291,
  1297,
  1301,
  1303,
  1307,
  1319,
  1321,
  1327,
  1361,
  1367,
  1373,
  1381,
  1399,
  1409,
  1423,
  1427,
  1429,
  1433,
  1439,
  1447,
  1451,
  1453,
  1459,
  1471,
  1481,
  1483,
  1487,
  1489,
  1493,
  1499,
  1511,
  1523,
  1531,
  1543,
  1549,
  1553,
  1559,
  1567,
  1571,
  1579,
  1583,
  1597,
  1601,
  1607,
  1609,
  1613,
  1619,
  1621,
  1627,
  1637,
  1657,
  1663,
  1667,
  1669,
  1693,
  1697,
  1699,
  1709,
  1721,
  1723,
  1733,
  1741,
  1747,
  1753,
  1759,
  1777,
  1783,
  1787,
  1789,
  1801,
  1811,
  1823,
  1831,
  1847,
  1861,
  1867,
  1871,
  1873,
  1877,
  1879,
  1889,
  1901,
  1907,
  1913,
  1931,
  1933,
  1949,
  1951,
  1973,
  1979,
  1987,
  1993,
  1997,
  1999,
  2003,
  2011,
  2017,
  2027,
  2029,
  2039,
  2053,
  2063,
  2069,
  2081,
  2083,
  2087,
  2089,
  2099,
  2111,
  2113,
  2129,
  2131,
  2137,
  2141,
  2143,
  2153,
  2161,
  2179,
  2203,
  2207,
  2213,
  2221,
  2237,
  2239,
  2243,
  2251,
  2267,
  2269,
  2273,
  2281,
  2287,
  2293,
  2297,
  2309,
  2311,
  2333,
  2339,
  2341,
  2347,
  2351,
  2357,
  2371,
  2377,
  2381,
  2383,
  2389,
  2393,
  2399,
  2411,
  2417,
  2423,
  2437,
  2441,
  2447,
  2459,
  2467,
  2473,
  2477,
  2503,
  2521,
  2531,
  2539,
  2543,
  2549,
  2551,
  2557,
  2579,
  2591,
  2593,
  2609,
  2617,
  2621,
  2633,
  2647,
  2657,
  2659,
  2663,
  2671,
  2677,
  2683,
  2687,
  2689,
  2693,
  2699,
  2707,
  2711,
  2713,
  2719,
  2729,
  2731,
  2741,
  2749,
  2753,
  2767,
  2777,
  2789,
  2791,
  2797,
  2801,
  2803,
  2819,
  2833,
  2837,
  2843,
  2851,
  2857,
  2861,
  2879,
  2887,
  2897,
  2903,
  2909,
  2917,
  2927,
  2939,
  2953,
  2957,
  2963,
  2969,
  2971,
  2999,
  3001,
  3011,
  3019,
  3023,
  3037,
  3041,
  3049,
  3061,
  3067,
  3079,
  3083,
  3089,
  3109,
  3119,
  3121,
  3137,
  3163,
  3167,
  3169,
  3181,
  3187,
  3191,
  3203,
  3209,
  3217,
  3221,
  3229,
  3251,
  3253,
  3257,
  3259,
  3271,
  3299,
  3301,
  3307,
  3313,
  3319,
  3323,
  3329,
  3331,
  3343,
  3347,
  3359,
  3361,
  3371,
  3373,
  3389,
  3391,
  3407,
  3413,
  3433,
  3449,
  3457,
  3461,
  3463,
  3467,
  3469,
  3491,
  3499,
  3511,
  3517,
  3527,
  3529,
  3533,
  3539,
  3541,
  3547,
  3557,
  3559,
  3571,
  3581,
  3583,
  3593,
  3607,
  3613,
  3617,
  3623,
  3631,
  3637,
  3643,
  3659,
  3671,
  3673,
  3677,
  3691,
  3697,
  3701,
  3709,
  3719,
  3727,
  3733,
  3739,
  3761,
  3767,
  3769,
  3779,
  3793,
  3797,
  3803,
  3821,
  3823,
  3833,
  3847,
  3851,
  3853,
  3863,
  3877,
  3881,
  3889,
  3907,
  3911,
  3917,
  3919,
  3923,
  3929,
  3931,
  3943,
  3947,
  3967,
  3989,
  4001,
  4003,
  4007,
  4013,
  4019,
  4021,
  4027,
  4049,
  4051,
  4057,
  4073,
  4079,
  4091,
  4093,
  4099,
  4111,
  4127,
  4129,
  4133,
  4139,
  4153,
  4157,
  4159,
  4177,
  4201,
  4211,
  4217,
  4219,
  4229,
  4231,
  4241,
  4243,
  4253,
  4259,
  4261,
  4271,
  4273,
  4283,
  4289,
  4297,
  4327,
  4337,
  4339,
  4349,
  4357,
  4363,
  4373,
  4391,
  4397,
  4409,
  4421,
  4423,
  4441,
  4447,
  4451,
  4457,
  4463,
  4481,
  4483,
  4493,
  4507,
  4513,
  4517,
  4519,
  4523,
  4547,
  4549,
  4561,
  4567,
  4583,
  4591,
  4597,
  4603,
  4621,
  4637,
  4639,
  4643,
  4649,
  4651,
  4657,
  4663,
  4673,
  4679,
  4691,
  4703,
  4721,
  4723,
  4729,
  4733,
  4751,
  4759,
  4783,
  4787,
  4789,
  4793,
  4799,
  4801,
  4813,
  4817,
  4831,
  4861,
  4871,
  4877,
  4889,
  4903,
  4909,
  4919,
  4931,
  4933,
  4937,
  4943,
  4951,
  4957,
  4967,
  4969,
  4973,
  4987,
  4993,
  4999,
  5003,
  5009,
  5011,
  5021,
  5023,
  5039,
  5051,
  5059,
  5077,
  5081,
  5087,
  5099,
  5101,
  5107,
  5113,
  5119,
  5147,
  5153,
  5167,
  5171,
  5179,
  5189,
  5197,
  5209,
  5227,
  5231,
  5233,
  5237,
  5261,
  5273,
  5279,
  5281,
  5297,
  5303,
  5309,
  5323,
  5333,
  5347,
  5351,
  5381,
  5387,
  5393,
  5399,
  5407,
  5413,
  5417,
  5419,
  5431,
  5437,
  5441,
  5443,
  5449,
  5471,
  5477,
  5479,
  5483,
  5501,
  5503,
  5507,
  5519,
  5521,
  5527,
  5531,
  5557,
  5563,
  5569,
  5573,
  5581,
  5591,
  5623,
  5639,
  5641,
  5647,
  5651,
  5653,
  5657,
  5659,
  5669,
  5683,
  5689,
  5693,
  5701,
  5711,
  5717,
  5737,
  5741,
  5743,
  5749,
  5779,
  5783,
  5791,
  5801,
  5807,
  5813,
  5821,
  5827,
  5839,
  5843,
  5849,
  5851,
  5857,
  5861,
  5867,
  5869,
  5879,
  5881,
  5897,
  5903,
  5923,
  5927,
  5939,
  5953,
  5981,
  5987,
  6007,
  6011,
  6029,
  6037,
  6043,
  6047,
  6053,
  6067,
  6073,
  6079,
  6089,
  6091,
  6101,
  6113,
  6121,
  6131,
  6133,
  6143,
  6151,
  6163,
  6173,
  6197,
  6199,
  6203,
  6211,
  6217,
  6221,
  6229,
  6247,
  6257,
  6263,
  6269,
  6271,
  6277,
  6287,
  6299,
  6301,
  6311,
  6317,
  6323,
  6329,
  6337,
  6343,
  6353,
  6359,
  6361,
  6367,
  6373,
  6379,
  6389,
  6397,
  6421,
  6427,
  6449,
  6451,
  6469,
  6473,
  6481,
  6491,
  6521,
  6529,
  6547,
  6551,
  6553,
  6563,
  6569,
  6571,
  6577,
  6581,
  6599,
  6607,
  6619,
  6637,
  6653,
  6659,
  6661,
  6673,
  6679,
  6689,
  6691,
  6701,
  6703,
  6709,
  6719,
  6733,
  6737,
  6761,
  6763,
  6779,
  6781,
  6791,
  6793,
  6803,
  6823,
  6827,
  6829,
  6833,
  6841,
  6857,
  6863,
  6869,
  6871,
  6883,
  6899,
  6907,
  6911,
  6917,
  6947,
  6949,
  6959,
  6961,
  6967,
  6971,
  6977,
  6983,
  6991,
  6997,
  7001,
  7013,
  7019,
  7027,
  7039,
  7043,
  7057,
  7069,
  7079,
  7103,
  7109,
  7121,
  7127,
  7129,
  7151,
  7159,
  7177,
  7187,
  7193,
  7207,
  7211,
  7213,
  7219,
  7229,
  7237,
  7243,
  7247,
  7253,
  7283,
  7297,
  7307,
  7309,
  7321,
  7331,
  7333,
  7349,
  7351,
  7369,
  7393,
  7411,
  7417,
  7433,
  7451,
  7457,
  7459,
  7477,
  7481,
  7487,
  7489,
  7499,
  7507,
  7517,
  7523,
  7529,
  7537,
  7541,
  7547,
  7549,
  7559,
  7561,
  7573,
  7577,
  7583,
  7589,
  7591,
  7603,
  7607,
  7621,
  7639,
  7643,
  7649,
  7669,
  7673,
  7681,
  7687,
  7691,
  7699,
  7703,
  7717,
  7723,
  7727,
  7741,
  7753,
  7757,
  7759,
  7789,
  7793,
  7817,
  7823,
  7829,
  7841,
  7853,
  7867,
  7873,
  7877,
  7879,
  7883,
  7901,
  7907,
  7919,
  7927,
  7933,
  7937,
  7949,
  7951,
  7963,
  7993,
  8009,
  8011,
  8017,
  8039,
  8053,
  8059,
  8069,
  8081,
  8087,
  8089,
  8093,
  8101,
  8111,
  8117,
  8123,
  8147,
  8161,
  8167,
  8171,
  8179,
  8191,
  8209,
  8219,
  8221,
  8231,
  8233,
  8237,
  8243,
  8263,
  8269,
  8273,
  8287,
  8291,
  8293,
  8297,
  8311,
  8317,
  8329,
  8353,
  8363,
  8369,
  8377,
  8387,
  8389,
  8419,
  8423,
  8429,
  8431,
  8443,
  8447,
  8461,
  8467,
  8501,
  8513,
  8521,
  8527,
  8537,
  8539,
  8543,
  8563,
  8573,
  8581,
  8597,
  8599,
  8609,
  8623,
  8627,
  8629,
  8641,
  8647,
  8663,
  8669,
  8677,
  8681,
  8689,
  8693,
  8699,
  8707,
  8713,
  8719,
  8731,
  8737,
  8741,
  8747,
  8753,
  8761,
  8779,
  8783,
  8803,
  8807,
  8819,
  8821,
  8831,
  8837,
  8839,
  8849,
  8861,
  8863,
  8867,
  8887,
  8893,
  8923,
  8929,
  8933,
  8941,
  8951,
  8963,
  8969,
  8971,
  8999,
  9001,
  9007,
  9011,
  9013,
  9029,
  9041,
  9043,
  9049,
  9059,
  9067,
  9091,
  9103,
  9109,
  9127,
  9133,
  9137,
  9151,
  9157,
  9161,
  9173,
  9181,
  9187,
  9199,
  9203,
  9209,
  9221,
  9227,
  9239,
  9241,
  9257,
  9277,
  9281,
  9283,
  9293,
  9311,
  9319,
  9323,
  9337,
  9341,
  9343,
  9349,
  9371,
  9377,
  9391,
  9397,
  9403,
  9413,
  9419,
  9421,
  9431,
  9433,
  9437,
  9439,
  9461,
  9463,
  9467,
  9473,
  9479,
  9491,
  9497,
  9511,
  9521,
  9533,
  9539,
  9547,
  9551,
  9587,
  9601,
  9613,
  9619,
  9623,
  9629,
  9631,
  9643,
  9649,
  9661,
  9677,
  9679,
  9689,
  9697,
  9719,
  9721,
  9733,
  9739,
  9743,
  9749,
  9767,
  9769,
  9781,
  9787,
  9791,
  9803,
  9811,
  9817,
  9829,
  9833,
  9839,
  9851,
  9857,
  9859,
  9871,
  9883,
  9887,
  9901,
  9907,
  9923,
  9929,
  9931,
  9941,
  9949,
  9967,
  9973
];

function power(x, y, p) {
  let res = 1;
  x = x % p;
  while (y > 0) {
    if (y & 1)
      res = (res*x) % p;
    y = y>>1;
    x = (x*x) % p;
  }
  return res;
}

function miillerTest(d, n) {
  let a = 2 + Math.floor(Math.random() * (n-2)) % (n - 4);
  let x = power(a, d, n);

  if (x == 1 || x == n-1)
    return true;

  while (d != n-1) {
    x = (x * x) % n;
    d *= 2;

    if (x == 1)
      return false;
    if (x == n-1)
        return true;
  }
  return false;
}

function isPrime(n, k = 50) {
  if (n <= 1 || n == 4) return false;
  if (n <= 3) return true;
  if (smallPrimes.includes(n)) return true;

  let d = n - 1;
  while (d % 2 == 0)
    d /= 2;

  for (let i = 0; i < k; i++)
    if (!miillerTest(d, n))
      return false;

  return true;
}

const bitLength = n => {
  let i = 0;
  while (n != 0n) {
    n >>= 1n;
    i++;
  }
  return i;
};

const factor = input => {
  let n = input;
  for (let p of smallPrimes) {
    p = BigInt(p);
    if (n % p == 0n) {
      return [p, n / p];
    }
  }

  if (n < 100000000n) {
    return [n];
  }

  console.log ('Staring quadratic sieve...');

  const n_bitLength = bitLength (n);
  console.log ('n =', n, '(', n_bitLength, 'bits)');

  const ceil_sqrt_n = ceil_sqrt (n);
  const block_size = 256;
  const max_offset = Number.MAX_SAFE_INTEGER - block_size;

  const factor_basis_size = Math.trunc (2 ** (n_bitLength / 32) * 96);
  const b_primes = [2];

  for (let i = 3; i < Number.MAX_SAFE_INTEGER; i += 2) {
    if (b_primes.length == factor_basis_size) break;
    if (!isPrime(i)) continue;
    if (isQuadraticResidue (n, BigInt(i))) {
      b_primes.push (i);
    }
  }
  console.log ('factor basis primes:', b_primes);
  const k2 = b_primes.length;

  console.log ('Initialization done...');

  // solve equation for each prime p
  const p_divisibles = [];
  for (let i = 0; i < k2; i++) {
    const p = b_primes[i];

    const minus_ceil_sqrt_n = (Number((0n - ceil_sqrt_n) % BigInt(p)) + p) % p;
    const sqrt_1 = Number(modular_sqrt(n, BigInt(p)));
    const sqrt_2 = p - sqrt_1;

    p_divisibles[i] = [];
    p_divisibles[i][0] = (sqrt_1 + minus_ceil_sqrt_n) % p;
    if (sqrt_2 != sqrt_1) {
      p_divisibles[i][1] = (sqrt_2 + minus_ceil_sqrt_n) % p;
    }
  }

  console.log ('Solved basic polynominal over the factor basis...');

  let smoothCounter = 0;
  //const smoothValues = [];
  const smoothFactors = [];
  const a = [];

  // This is the most costly part
  main_loop:
  for (let offset = 0; offset < max_offset; offset += block_size) {
    //const vector = [];
    const tmp_vector = [];
    const tmp_factors = [];

    for (let i = 0; i < block_size; i++) {
      tmp_vector[i] = (ceil_sqrt_n + BigInt(i) + BigInt(offset)) ** 2n - n;
      //tmp_vector[i] = vector[i];
      tmp_factors[i] = new Uint32Array (k2);
    }

    for (let i = 0; i < k2; i++) {
      const p = b_primes[i];
      const start = p_divisibles[i].map (x => (p - ((p - x + offset % p) % p)) % p);

      for (let js = start; js.some (j => j < block_size); js = js.map (j => j + p)) {
        for (let j of js) {
          if (j < block_size) {
            do {
              tmp_factors[j][i]++;
              tmp_vector[j] = tmp_vector[j] / BigInt(p);
            } while (tmp_vector[j] % BigInt(p) == 0n);

            if (tmp_vector[j] == 1n) {
              smoothFactors[smoothCounter] = tmp_factors[j];
              a[smoothCounter] = ceil_sqrt_n + BigInt(j) + BigInt(offset);

              smoothCounter++;
              if (smoothCounter > k2) {
                break main_loop;
              }

              console.log (smoothCounter, 'roots...');
            }
          }
        }
      }
    }
  }

  let k3 = smoothFactors.length;
  console.log ('Sieving done: ' + k3 + ' B-smooth square roots modulo n');

  console.log ('matrix:', k2 + ' * ' + k3, '=', k2 * k3);
  const bits = new BitMatrix (k2, k3);
  for (let i = 0; i < k2; i++) {
    for (let j = 0; j < k3; j++) {
      bits.set (i, j, smoothFactors[j][i]);
    }
  }

  const kernel = bits.getKernel ();
  const rank = bits.rank;

  console.log ('Done calculating linear algebra over finite field...');
  console.log ('reduced matrix:', 'rank =', rank);

  console.log ('nontrivial dependencies:', kernel.length);
  for (let basis of kernel) {
    console.log ('A vector of the basis of the kernel:', ... basis);
    let e = new Uint32Array (k2);
    let x = 1n;
    const roots = [];
    for (let j = 0; j < k3; j++) {
      if (0 == basis[j]) continue;

      roots.push (a[j]);
      x = (x * a[j]) % n;
      for (let i = 0; i < k2; i++) {
        e[i] += smoothFactors[j][i];
      }
    }

    let y = 1n;
    for (let i = 0; i < k2; i++) {
      y = (modPow(BigInt(b_primes[i]), BigInt(e[i] >> 1), n) * y) % n;
    }

    const comparison = (n - y) != x;
    if (comparison && x != y) {
      console.log ('roots:', ... roots);
      console.log ('factors:', ... e);
      console.log ('x:', x, 'y:', y);

      const p = gcd(x - y, n);
      const q = gcd(x + y, n);
      console.log ('factorization done:', p, q);
      console.log ('Finished!');
      return [p, q];
    } else {
      console.log ('skipping trivial factors');
    }
  }

  console.log ('giving up:', n.value);
  return [n];
};

self.onmessage = (ev) => {
  const n = ev.data;
  const factors = factor(n);
  self.postMessage(factors);
};
self.postMessage(true);
