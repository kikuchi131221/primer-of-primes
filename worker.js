/* worker.js */

// 設定: 素数リストの上限
const PRIME_LIMIT = 100000;
let smallPrimes = [];

// 1. エラトステネスの篩で素数リストを生成
function generatePrimes(limit) {
    const isPrime = new Uint8Array(limit + 1).fill(1);
    isPrime[0] = isPrime[1] = 0;
    for (let p = 2; p * p <= limit; p++) {
        if (isPrime[p]) {
            for (let i = p * p; i <= limit; i += p) {
                isPrime[i] = 0;
            }
        }
    }
    const primes = [];
    for (let i = 0; i <= limit; i++) {
        if (isPrime[i]) primes.push(BigInt(i));
    }
    return primes;
}

// 初期化（Worker起動時に一度だけ実行）
smallPrimes = generatePrimes(PRIME_LIMIT);

// 2. ユーティリティ関数
function gcd(a, b) {
    while (b > 0n) {
        let temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

// べき乗剰余 (base^exp % mod) を高速に計算
function modPow(base, exp, mod) {
    let res = 1n;
    base %= mod;
    while (exp > 0n) {
        if (exp % 2n === 1n) res = (res * base) % mod;
        base = (base * base) % mod;
        exp /= 2n;
    }
    return res;
}

// 範囲指定の乱数 (BigInt用)
// Math.random()は0-1のdoubleなので、簡易的に生成します
function randBigInt(min, max) {
    const range = max - min;
    // 簡易的な実装: 精度は落ちますが、ポラードのロー法には十分です
    // 非常に大きな範囲の場合、偏りが出ますが今回の用途では許容範囲です
    const randNum = BigInt(Math.floor(Math.random() * Number.MAX_SAFE_INTEGER));
    return (randNum % range) + min;
}

// 3. ミラー・ラビン素数判定
function isPrimeMillerRabin(n, k = 5) {
    if (n < 2n) return false;
    if (n === 2n || n === 3n) return true;
    if (n % 2n === 0n) return false;

    let d = n - 1n;
    let r = 0n;
    while (d % 2n === 0n) {
        d /= 2n;
        r += 1n;
    }

    for (let i = 0; i < k; i++) {
        const a = randBigInt(2n, n - 2n);
        let x = modPow(a, d, n);
        if (x === 1n || x === n - 1n) continue;
        let continueLoop = false;
        for (let j = 0n; j < r - 1n; j++) {
            x = (x * x) % n;
            if (x === n - 1n) {
                continueLoop = true;
                break;
            }
        }
        if (!continueLoop) return false;
    }
    return true;
}

// 4. ポラードのロー法 (合成数の因数を見つける)
function pollardRho(n) {
    if (n % 2n === 0n) return 2n;
    let x = randBigInt(2n, n - 1n);
    let y = x;
    let c = randBigInt(1n, n - 1n);
    let g = 1n;

    while (g === 1n) {
        x = (x * x + c) % n;
        y = (y * y + c) % n;
        y = (y * y + c) % n; // yは2回進む
        
        let diff = x > y ? x - y : y - x;
        g = gcd(diff, n);
        
        if (g === n) {
            // 失敗したら乱数の種を変えて再試行
            return pollardRho(n);
        }
    }
    return g;
}

// 5. メインの分解ロジック
function factorize(n) {
    const factors = {};

    // 小さな素数で割り切れるだけ割る
    for (const p of smallPrimes) {
        if (p * p > n) break;
        while (n % p === 0n) {
            factors[p] = (factors[p] || 0) + 1;
            n /= p;
        }
    }

    if (n === 1n) return factors;

    // 残りを再帰的に分解
    const stack = [n];
    while (stack.length > 0) {
        const target = stack.pop();
        if (target === 1n) continue;

        if (isPrimeMillerRabin(target)) {
            factors[target] = (factors[target] || 0) + 1;
            continue;
        }

        const factor = pollardRho(target);
        stack.push(factor);
        stack.push(target / factor);
    }
    
    // BigIntのキーを数値順にソートして返す
    // ※ObjectのキーはStringになるため、後で変換が必要
    return factors;
}

// メッセージ受信ハンドラ
self.onmessage = function(e) {
    const inputStr = e.data; // 文字列として受け取る
    try {
        const n = BigInt(inputStr);
        const startTime = performance.now();
        const result = factorize(n);
        const endTime = performance.now();

        // 結果を整形してメインスレッドへ送信
        self.postMessage({
            status: 'success',
            original: inputStr,
            factors: result,
            time: (endTime - startTime).toFixed(2)
        });
    } catch (err) {
        self.postMessage({
            status: 'error',
            message: '無効な数値です: ' + err.message
        });
    }
};
