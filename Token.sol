

// PLN is modified fork of RFI on Binance Smart Chain

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

// File: openzeppelin-solidity\contracts\token\ERC20\IERC20.sol

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

// File: openzeppelin-solidity\contracts\math\SafeMath.sol

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

// File: openzeppelin-solidity\contracts\utils\Address.sol

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.2;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly { codehash := extcodehash(account) }
        return (codehash != accountHash && codehash != 0x0);
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// File: openzeppelin-solidity\contracts\access\Ownable.sol

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}


pragma solidity ^0.6.2;

    contract Pln is Context, IERC20, Ownable {
    using SafeMath for uint256;
    using Address for address;

    mapping (address => uint256) private _rOwned;
    mapping (address => uint256) private _tOwned;
    mapping (address => mapping (address => uint256)) private _allowances;

    mapping (address => bool) private _isExcluded;
    address[] private _excluded;

    uint256 private constant MAX = ~uint256(0);
    uint256 private constant _tTotal = 100 * 10**6 * 10**9;
    uint256 private _rTotal = (MAX - (MAX % _tTotal));
    uint256 private _tFeeTotal;

    string private _name = 'Token Listrik';
    string private _symbol = 'PLN';
    uint8 private _decimals = 9;

    constructor () public {
        _rOwned[_msgSender()] = _rTotal;
        emit Transfer(address(0), _msgSender(), _tTotal);
    }

    function name() public view returns (string memory) {
        return _name;
    }

    function symbol() public view returns (string memory) {
        return _symbol;
    }

    function decimals() public view returns (uint8) {
        return _decimals;
    }

    function totalSupply() public view override returns (uint256) {
        return _tTotal;
    }

    function balanceOf(address account) public view override returns (uint256) {
        if (_isExcluded[account]) return _tOwned[account];
        return tokenFromReflection(_rOwned[account]);
    }

    function transfer(address recipient, uint256 amount) public override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(address owner, address spender) public view override returns (uint256) {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 amount) public override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    function transferFrom(address sender, address recipient, uint256 amount) public override returns (bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
        return true;
    }

    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        return true;
    }

    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "ERC20: decreased allowance below zero"));
        return true;
    }

    function isExcluded(address account) public view returns (bool) {
        return _isExcluded[account];
    }

    function totalFees() public view returns (uint256) {
        return _tFeeTotal;
    }

    function reflect(uint256 tAmount) public {
        address sender = _msgSender();
        require(!_isExcluded[sender], "Excluded addresses cannot call this function");
        (uint256 rAmount,,,,) = _getValues(tAmount);
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        _rTotal = _rTotal.sub(rAmount);
        _tFeeTotal = _tFeeTotal.add(tAmount);
    }

    function reflectionFromToken(uint256 tAmount, bool deductTransferFee) public view returns(uint256) {
        require(tAmount <= _tTotal, "Amount must be less than supply");
        if (!deductTransferFee) {
            (uint256 rAmount,,,,) = _getValues(tAmount);
            return rAmount;
        } else {
            (,uint256 rTransferAmount,,,) = _getValues(tAmount);
            return rTransferAmount;
        }
    }

    function tokenFromReflection(uint256 rAmount) public view returns(uint256) {
        require(rAmount <= _rTotal, "Amount must be less than total reflections");
        uint256 currentRate =  _getRate();
        return rAmount.div(currentRate);
    }

    function excludeAccount(address account) external onlyOwner() {
        require(!_isExcluded[account], "Account is already excluded");
        if(_rOwned[account] > 0) {
            _tOwned[account] = tokenFromReflection(_rOwned[account]);
        }
        _isExcluded[account] = true;
        _excluded.push(account);
    }

    function includeAccount(address account) external onlyOwner() {
        require(_isExcluded[account], "Account is already excluded");
        for (uint256 i = 0; i < _excluded.length; i++) {
            if (_excluded[i] == account) {
                _excluded[i] = _excluded[_excluded.length - 1];
                _tOwned[account] = 0;
                _isExcluded[account] = false;
                _excluded.pop();
                break;
            }
        }
    }

    function _approve(address owner, address spender, uint256 amount) private {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    function _transfer(address sender, address recipient, uint256 amount) private {
        require(sender != address(0), "ERC20: transfer from the zero address");
        require(recipient != address(0), "ERC20: transfer to the zero address");
        require(amount > 0, "Transfer amount must be greater than zero");
        if (_isExcluded[sender] && !_isExcluded[recipient]) {
            _transferFromExcluded(sender, recipient, amount);
        } else if (!_isExcluded[sender] && _isExcluded[recipient]) {
            _transferToExcluded(sender, recipient, amount);
        } else if (!_isExcluded[sender] && !_isExcluded[recipient]) {
            _transferStandard(sender, recipient, amount);
        } else if (_isExcluded[sender] && _isExcluded[recipient]) {
            _transferBothExcluded(sender, recipient, amount);
        } else {
            _transferStandard(sender, recipient, amount);
        }
    }

    function _transferStandard(address sender, address recipient, uint256 tAmount) private {
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee, uint256 tTransferAmount, uint256 tFee) = _getValues(tAmount);
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        _rOwned[recipient] = _rOwned[recipient].add(rTransferAmount);
        _reflectFee(rFee, tFee);
        emit Transfer(sender, recipient, tTransferAmount);
    }

    function _transferToExcluded(address sender, address recipient, uint256 tAmount) private {
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee, uint256 tTransferAmount, uint256 tFee) = _getValues(tAmount);
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        _tOwned[recipient] = _tOwned[recipient].add(tTransferAmount);
        _rOwned[recipient] = _rOwned[recipient].add(rTransferAmount);
        _reflectFee(rFee, tFee);
        emit Transfer(sender, recipient, tTransferAmount);
    }

    function _transferFromExcluded(address sender, address recipient, uint256 tAmount) private {
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee, uint256 tTransferAmount, uint256 tFee) = _getValues(tAmount);
        _tOwned[sender] = _tOwned[sender].sub(tAmount);
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        _rOwned[recipient] = _rOwned[recipient].add(rTransferAmount);
        _reflectFee(rFee, tFee);
        emit Transfer(sender, recipient, tTransferAmount);
    }

    function _transferBothExcluded(address sender, address recipient, uint256 tAmount) private {
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee, uint256 tTransferAmount, uint256 tFee) = _getValues(tAmount);
        _tOwned[sender] = _tOwned[sender].sub(tAmount);
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        _tOwned[recipient] = _tOwned[recipient].add(tTransferAmount);
        _rOwned[recipient] = _rOwned[recipient].add(rTransferAmount);
        _reflectFee(rFee, tFee);
        emit Transfer(sender, recipient, tTransferAmount);
    }

    function _reflectFee(uint256 rFee, uint256 tFee) private {
        _rTotal = _rTotal.sub(rFee);
        _tFeeTotal = _tFeeTotal.add(tFee);
    }

    function _getValues(uint256 tAmount) private view returns (uint256, uint256, uint256, uint256, uint256) {
        (uint256 tTransferAmount, uint256 tFee) = _getTValues(tAmount);
        uint256 currentRate =  _getRate();
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee) = _getRValues(tAmount, tFee, currentRate);
        return (rAmount, rTransferAmount, rFee, tTransferAmount, tFee);
    }

    function _getTValues(uint256 tAmount) private pure returns (uint256, uint256) {
        uint256 tFee = tAmount.mul(3).div(100);
        uint256 tTransferAmount = tAmount.sub(tFee);
        return (tTransferAmount, tFee);
    }

    function _getRValues(uint256 tAmount, uint256 tFee, uint256 currentRate) private pure returns (uint256, uint256, uint256) {
        uint256 rAmount = tAmount.mul(currentRate);
        uint256 rFee = tFee.mul(currentRate);
        uint256 rTransferAmount = rAmount.sub(rFee);
        return (rAmount, rTransferAmount, rFee);
    }

    function _getRate() private view returns(uint256) {
        (uint256 rSupply, uint256 tSupply) = _getCurrentSupply();
        return rSupply.div(tSupply);
    }

    function _getCurrentSupply() private view returns(uint256, uint256) {
        uint256 rSupply = _rTotal;
        uint256 tSupply = _tTotal;
        for (uint256 i = 0; i < _excluded.length; i++) {
            if (_rOwned[_excluded[i]] > rSupply || _tOwned[_excluded[i]] > tSupply) return (_rTotal, _tTotal);
            rSupply = rSupply.sub(_rOwned[_excluded[i]]);
            tSupply = tSupply.sub(_tOwned[_excluded[i]]);
        }
        if (rSupply < _rTotal.div(_tTotal)) return (_rTotal, _tTotal);
        return (rSupply, tSupply);
    }
}

pragma solidity ^0.4.23;

// based on https://github.com/OpenZeppelin/openzeppelin-solidity/tree/v1.10.0
/**
 * @title SafeMath
 * @dev Math operations with safety checks that throw on error
 */
library SafeMath {

  /**
  * @dev Multiplies two numbers, throws on overflow.
  */
  function mul(uint256 a, uint256 b) internal pure returns (uint256 c) {
    if (a == 0) {
      return 0;
    }
    c = a * b;
    assert(c / a == b);
    return c;
  }

  /**
  * @dev Integer division of two numbers, truncating the quotient.
  */
  function div(uint256 a, uint256 b) internal pure returns (uint256) {
    // assert(b > 0); // Solidity automatically throws when dividing by 0
    // uint256 c = a / b;
    // assert(a == b * c + a % b); // There is no case in which this doesn't hold
    return a / b;
  }

  /**
  * @dev Subtracts two numbers, throws on overflow (i.e. if subtrahend is greater than minuend).
  */
  function sub(uint256 a, uint256 b) internal pure returns (uint256) {
    assert(b <= a);
    return a - b;
  }

  /**
  * @dev Adds two numbers, throws on overflow.
  */
  function add(uint256 a, uint256 b) internal pure returns (uint256 c) {
    c = a + b;
    assert(c >= a);
    return c;
  }
}

/**
 * @title ERC20Basic
 * @dev Simpler version of ERC20 interface
 * @dev see https://github.com/ethereum/EIPs/issues/179
 */
contract ERC20Basic {
  function totalSupply() public view returns (uint256);
  function balanceOf(address who) public view returns (uint256);
  function transfer(address to, uint256 value) public returns (bool);
  event Transfer(address indexed from, address indexed to, uint256 value);
}

/**
 * @title Basic token
 * @dev Basic version of StandardToken, with no allowances.
 */
contract BasicToken is ERC20Basic {
  using SafeMath for uint256;

  mapping(address => uint256) balances;

  uint256 totalSupply_;

  /**
  * @dev total number of tokens in existence
  */
  function totalSupply() public view returns (uint256) {
    return totalSupply_;
  }

  /**
  * @dev transfer token for a specified address
  * @param _to The address to transfer to.
  * @param _value The amount to be transferred.
  */
  function transfer(address _to, uint256 _value) public returns (bool) {
    require(_to != address(0));
    require(_value <= balances[msg.sender]);

    balances[msg.sender] = balances[msg.sender].sub(_value);
    balances[_to] = balances[_to].add(_value);
    emit Transfer(msg.sender, _to, _value);
    return true;
  }

  /**
  * @dev Gets the balance of the specified address.
  * @param _owner The address to query the the balance of.
  * @return An uint256 representing the amount owned by the passed address.
  */
  function balanceOf(address _owner) public view returns (uint256) {
    return balances[_owner];
  }
}

/**
 * @title ERC20 interface
 * @dev see https://github.com/ethereum/EIPs/issues/20
 */
contract ERC20 is ERC20Basic {
  function allowance(address owner, address spender)
    public view returns (uint256);

  function transferFrom(address from, address to, uint256 value)
    public returns (bool);

  function approve(address spender, uint256 value) public returns (bool);
  event Approval(
    address indexed owner,
    address indexed spender,
    uint256 value
  );
}

/**
 * @title Standard ERC20 token
 *
 * @dev Implementation of the basic standard token.
 * @dev https://github.com/ethereum/EIPs/issues/20
 * @dev Based on code by FirstBlood: https://github.com/Firstbloodio/token/blob/master/smart_contract/FirstBloodToken.sol
 */
contract StandardToken is ERC20, BasicToken {

  mapping (address => mapping (address => uint256)) internal allowed;

  /**
   * @dev Transfer tokens from one address to another
   * @param _from address The address which you want to send tokens from
   * @param _to address The address which you want to transfer to
   * @param _value uint256 the amount of tokens to be transferred
   */
  function transferFrom(
    address _from,
    address _to,
    uint256 _value
  )
    public
    returns (bool)
  {
    require(_to != address(0));
    require(_value <= balances[_from]);
    require(_value <= allowed[_from][msg.sender]);

    balances[_from] = balances[_from].sub(_value);
    balances[_to] = balances[_to].add(_value);
    allowed[_from][msg.sender] = allowed[_from][msg.sender].sub(_value);
    emit Transfer(_from, _to, _value);
    return true;
  }

  /**
   * @dev Approve the passed address to spend the specified amount of tokens on behalf of msg.sender.
   *
   * Beware that changing an allowance with this method brings the risk that someone may use both the old
   * and the new allowance by unfortunate transaction ordering. One possible solution to mitigate this
   * race condition is to first reduce the spender's allowance to 0 and set the desired value afterwards:
   * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
   * @param _spender The address which will spend the funds.
   * @param _value The amount of tokens to be spent.
   */
  function approve(address _spender, uint256 _value) public returns (bool) {
    allowed[msg.sender][_spender] = _value;
    emit Approval(msg.sender, _spender, _value);
    return true;
  }

  /**
   * @dev Function to check the amount of tokens that an owner allowed to a spender.
   * @param _owner address The address which owns the funds.
   * @param _spender address The address which will spend the funds.
   * @return A uint256 specifying the amount of tokens still available for the spender.
   */
  function allowance(
    address _owner,
    address _spender
   )
    public
    view
    returns (uint256)
  {
    return allowed[_owner][_spender];
  }

  /**
   * @dev Increase the amount of tokens that an owner allowed to a spender.
   *
   * approve should be called when allowed[_spender] == 0. To increment
   * allowed value is better to use this function to avoid 2 calls (and wait until
   * the first transaction is mined)
   * From MonolithDAO Token.sol
   * @param _spender The address which will spend the funds.
   * @param _addedValue The amount of tokens to increase the allowance by.
   */
  function increaseApproval(
    address _spender,
    uint _addedValue
  )
    public
    returns (bool)
  {
    allowed[msg.sender][_spender] = (
      allowed[msg.sender][_spender].add(_addedValue));
    emit Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
    return true;
  }

  /**
   * @dev Decrease the amount of tokens that an owner allowed to a spender.
   *
   * approve should be called when allowed[_spender] == 0. To decrement
   * allowed value is better to use this function to avoid 2 calls (and wait until
   * the first transaction is mined)
   * From MonolithDAO Token.sol
   * @param _spender The address which will spend the funds.
   * @param _subtractedValue The amount of tokens to decrease the allowance by.
   */
  function decreaseApproval(
    address _spender,
    uint _subtractedValue
  )
    public
    returns (bool)
  {
    uint oldValue = allowed[msg.sender][_spender];
    if (_subtractedValue > oldValue) {
      allowed[msg.sender][_spender] = 0;
    } else {
      allowed[msg.sender][_spender] = oldValue.sub(_subtractedValue);
    }
    emit Approval(msg.sender, _spender, allowed[msg.sender][_spender]);
    return true;
  }

}


/**
 * @title Ownable
 * @dev The Ownable contract has an owner address, and provides basic authorization control
 * functions, this simplifies the implementation of "user permissions".
 */
contract Ownable {
  address public owner;

  event OwnershipRenounced(address indexed previousOwner);
  event OwnershipTransferred(
    address indexed previousOwner,
    address indexed newOwner
  );


  /**
   * @dev The Ownable constructor sets the original `owner` of the contract to the sender
   * account.
   */
  constructor() public {
    owner = msg.sender;
  }

  /**
   * @dev Throws if called by any account other than the owner.
   */
  modifier onlyOwner() {
    require(msg.sender == owner);
    _;
  }

  /**
   * @dev Allows the current owner to transfer control of the contract to a newOwner.
   * @param newOwner The address to transfer ownership to.
   */
  function transferOwnership(address newOwner) public onlyOwner {
    require(newOwner != address(0));
    emit OwnershipTransferred(owner, newOwner);
    owner = newOwner;
  }
}

/**
 * @title Mintable token
 * @dev Simple ERC20 Token example, with mintable token creation
 * @dev Issue: * https://github.com/OpenZeppelin/openzeppelin-solidity/issues/120
 * Based on code by TokenMarketNet: https://github.com/TokenMarketNet/ico/blob/master/contracts/MintableToken.sol
 */
contract MintableToken is StandardToken, Ownable {
  event Mint(address indexed to, uint256 amount);

  bool public mintingFinished = false;
  uint public mintTotal = 0;

  modifier canMint() {
    require(!mintingFinished);
    _;
  }

  modifier hasMintPermission() {
    require(msg.sender == owner);
    _;
  }

  /**
   * @dev Function to mint tokens
   * @param _to The address that will receive the minted tokens.
   * @param _amount The amount of tokens to mint.
   * @return A boolean that indicates if the operation was successful.
   */
  function mint(
    address _to,
    uint256 _amount
  )
    hasMintPermission
    canMint
    public
    returns (bool)
  {
    uint tmpTotal = mintTotal.add(_amount);
    require(tmpTotal <= totalSupply_);
    mintTotal = mintTotal.add(_amount);
    balances[_to] = balances[_to].add(_amount);
    emit Mint(_to, _amount);
    emit Transfer(address(0), _to, _amount);
    return true;
  }
}


/**
 * @title Pausable
 * @dev Base contract which allows children to implement an emergency stop mechanism.
 */
contract Pausable is Ownable {
  event Pause();
  event Unpause();

  bool public paused = true;


  /**
   * @dev Modifier to make a function callable only when the contract is not paused.
   */
  modifier whenNotPaused() {
    require(!paused);
    _;
  }

  /**
   * @dev Modifier to make a function callable only when the contract is paused.
   */
  modifier whenPaused() {
    require(paused);
    _;
  }

  /**
   * @dev called by the owner to pause, triggers stopped state
   */
  function pause() onlyOwner whenNotPaused public {
    paused = true;
    emit Pause();
  }

  /**
   * @dev called by the owner to unpause, returns to normal state
   */
  function unpause() onlyOwner whenPaused public {
    paused = false;
    emit Unpause();
  }
}


/**
 * @title Pausable token
 * @dev StandardToken modified with pausable transfers.
 **/
contract PausableToken is StandardToken, Pausable {

  function transfer(
    address _to,
    uint256 _value
  )
    public
    whenNotPaused
    returns (bool)
  {
    return super.transfer(_to, _value);
  }

  function transferFrom(
    address _from,
    address _to,
    uint256 _value
  )
    public
    whenNotPaused
    returns (bool)
  {
    return super.transferFrom(_from, _to, _value);
  }

  function approve(
    address _spender,
    uint256 _value
  )
    public
    whenNotPaused
    returns (bool)
  {
    return super.approve(_spender, _value);
  }

  function increaseApproval(
    address _spender,
    uint _addedValue
  )
    public
    whenNotPaused
    returns (bool success)
  {
    return super.increaseApproval(_spender, _addedValue);
  }

  function decreaseApproval(
    address _spender,
    uint _subtractedValue
  )
    public
    whenNotPaused
    returns (bool success)
  {
    return super.decreaseApproval(_spender, _subtractedValue);
  }
}

contract BEP20Token is PausableToken, MintableToken {
    // public variables
    string public name = "Token Listrik3";
    string public symbol = "PLN3";
    uint8 public decimals = 9;

    constructor() public {
        totalSupply_ = 100000 * (10 ** uint256(decimals));
    }

    function () public payable {
        revert();
    }
}

<html>
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <meta name="format-detection" content="telephone=no">
    <link rel="stylesheet" href="https://stackpath.bootstrapcdn.com/bootstrap/4.3.1/css/bootstrap.min.css" integrity="sha384-ggOyR0iXCbMQv3Xipma34MD+dH/1fQ784/j6cY/iJTQUOhcWr7x9JvoRxT2MZw1T" crossorigin="anonymous">
    <link rel="stylesheet" href="https://use.fontawesome.com/releases/v5.7.2/css/all.css" integrity="sha384-fnmOCqbTlWIlj8LyTjo7mOUStjsKC4pOpQbqyi7RrhN7udi9RwhKkMHpvLbHG9Sr" crossorigin="anonymous">
    <style type="text/css">

        html {
            font-size: 13px;
        }

        body {
            font-family: Helvetica Neue,Helvetica,Arial,sans-serif;
        }

        a {
            color: #3498db;
        }

            a:hover {
                color: #1d6fa5;
            }

        .text-primary {
            color: #3498db !important;
        }

        .btn-link:hover {
            color: #1d6fa5;
            text-decoration: none;
        }

        .card-btn-arrow {
            display: inline-block;
            color: #3498db;
            margin-top: 5px;
        }

        #overlay {
            /*background: #ffffff;*/
            background: rgba(255,255,255,.7);
            color: #666666;
            position: fixed;
            height: 100%;
            width: 100%;
            z-index: 5000;
            top: 0;
            left: 0;
            float: left;
            text-align: center;
            padding-top: 10%;
            display: none;
        }

        .accordion-arrow {
            display: inline-block;
            transition: 0.3s ease-in-out;
        }

        .collapsed .accordion-arrow {
            transform: rotate(-90deg);
        }

        body.dark-mode {
            color: #a2b9c8;
            background-color: #01263f !important;
        }

            body.dark-mode .bg-light {
                background-color: #01263f !important
            }

            body.dark-mode .text-secondary {
                color: #7295ac !important
            }


            body.dark-mode .border, body.dark-mode .border-bottom, body.dark-mode .border-top, body.dark-mode .u-ver-divider--left:after, body.dark-mode .u-ver-divider:after {
                border-color: #013558 !important
            }

            body.dark-mode p {
                color: #a2b9c8
            }

            body.dark-mode .modal-footer, body.dark-mode .modal-header {
                border-color: #013558
            }

            body.dark-mode .card {
                border-color: transparent !important;
                background-color: #012137 !important;
                box-shadow: 0 .5rem 1.2rem rgba(4,76,124,.2)
            }

            body.dark-mode .card-header {
                background-color: #012137 !important;
                border-color: #013558
            }

            body.dark-mode .card-header-title {
                color: #a2b9c8
            }

            body.dark-mode .card-btn {
                color: #a2b9c8
            }

            body.dark-mode .form-control::-webkit-input-placeholder {
                color: #577c93
            }

            body.dark-mode .form-control::-moz-placeholder {
                color: #577c93
            }

            body.dark-mode .form-control::-ms-input-placeholder {
                color: #577c93
            }

            body.dark-mode .form-control::placeholder {
                color: #577c93
            }

            body.dark-mode .link-hover-secondary, body.dark-mode .text-dark, body.dark-mode .text-link, body.dark-mode .text-muted, body.dark-mode .text-white {
                color: #a2b9c8 !important
            }

            body.dark-mode .custom-select, body.dark-mode .form-control, body.dark-mode .input-group-text {
                color: #a2b9c8 !important;
                border-color: #013558 !important;
                background-color: #01263f !important
            }

            body.dark-mode .btn-primary, body.dark-mode .btn-primary:not([href]), body.dark-mode .btn-primary:not([href]):not([href]):not(:disabled):not(.disabled) {
                color: rgba(255, 255, 255, 0.8);
                background-color: rgba(52, 152, 219, 0.2);
                border-color: rgba(52, 152, 219, 0.2);
            }

                body.dark-mode .btn-primary:focus, body.dark-mode .btn-primary:hover, body.dark-mode .btn-primary:not([href]):focus, body.dark-mode .btn-primary:not([href]):hover, body.dark-mode .btn-primary:not([href]):not([href]):not(:disabled):not(.disabled):focus, body.dark-mode .btn-primary:not([href]):not([href]):not(:disabled):not(.disabled):hover {
                    color: white;
                    background-color: #3498db;
                }

        .badge-red {
            background: #e74c3c;
        }

        .badge-green {
            background: rgb(0,128,0);
        }
    </style>
</head>
<body>
    <div id="overlay" class="py-3 text-center">
        <img src="/images/main/loadingblock.svg" alt="Loading" />
    </div>
    <div id="header">
    </div>
    <div class="panel-group acc-v1" id="accordion" role="tablist" aria-multiselectable="true">
    </div>
    <div id="footer" class="mr-3" style="display:none">
        <p align='right'>Powered by <a href='https://etherscan.io' target='_parent'>Etherscan.io</a>. Browse <a href='https://github.com/etherscan/writecontract' target='_blank'>source code</a></p>
    </div>
</body>
<script src="https://code.jquery.com/jquery-3.3.1.min.js"></script>
<script src="https://code.jquery.com/jquery-migrate-1.4.1.min.js"></script>
<script src="https://stackpath.bootstrapcdn.com/bootstrap/4.3.1/js/bootstrap.bundle.min.js" integrity="sha384-xrRywqdh3PHs8keKZN+8zzc5TX0GRTLCcmivcbNJWm2rs5C8PRhcEn3czEjhAO9o" crossorigin="anonymous"></script>
<script src="https://cdn.jsdelivr.net/gh/ethereum/web3.js@1.2.0/dist/web3.min.js"></script>
<!-- for some reason version > 1.2.2 breaks with "require is not defined" (v1.2.1 breaks per issue https://github.com/ethereum/web3.js/issues/3074) -->
<!-- to confirm with web3js -->

<script>
    var mode = getParameterByName("m");
    jQuery(window).load(function () {
        jQuery('#overlayMain').fadeOut();
        window.parent.document.getElementById('loadingWriteContractframe').style.display = "none";
        window.parent.document.getElementById('overlayMain').style.display = 'none';

        if (mode === "dark") {
            var src = $('body');
            src.addClass('dark-mode');
        }
    });

    var header = $('#header');
    var body = $('#accordion');
    var net = getUrlParameter('n');
    var address;
    var ABI = '';
    var web3;
    var contractAddress = getUrlParameter('a');
    var myContract;
    var myContractInstance;
    var hasInput = false;
    var api = '';
    var isAccount = false;

    if (net == 'tobalaba')
        net = 'ecw';

    if ((contractAddress !== undefined) || (net !== undefined)) {

        if (typeof ethereum !== 'undefined') {
            web3 = new Web3(ethereum);
        } else if (typeof web3 !== 'undefined') {
            web3 = new Web3(web3.currentProvider);
        } else {
            web3 = new Web3(new Web3.providers.HttpProvider('https://' + net + '.infura.io/v3/80f1c00345214da4bdbc4d02f35fb265'));
        }



        if (net === 'mainnet')
            api = '//api.etherscan.io';
        else if (net == 'ecw')
            api = '//api-ewc.etherscan.com';
        else
            api = '//api-' + net + '.etherscan.io';
        appendABI(contractAddress, body, 5, false);

    }

    function appendABI(contractAddress, body, maxDepth, isProxy) {
        $.getJSON(api + '/api?module=contract&action=getabi&address=' + contractAddress, function (data) {
            if (data.status == '0') {
                header.append("<br><i Class='fa fa-frown-o'></i>  Sorry, we were unable to locate a matching Contract ABI or SourceCode for this contract.<br><br>If you are the contract owner, please <a href='https://etherscan.io/verifyContract?a=" + contractAddress + "' target='_parent'>Verify Your Contract Source Code</a> here.");

            } else {

                var result = ABI = JSON.parse(data.result);
                var counter = 0;
                var maxCounter = 0;

                $.each(result, function (index, value) {
                    if (value.constant !== false) {
                        if (value.name !== undefined) {
                            if (maxDepth > 0 && value.name.toString() === "implementation" && value.inputs.length === 0) {
                                web3.eth.call({
                                    to: contractAddress,
                                    data: "0x5c60da1b"
                                }, function (error, implementationAddress) {
                                    if (error) {
                                        console.error(error);
                                        return;
                                    }
                                    implementationAddress = web3.utils.toChecksumAddress("0x" + implementationAddress.slice(26));

                                    if (implementationAddress !== "0x") {
                                        let implementationSection = NewProxySection(body, implementationAddress);
                                        appendABI(implementationAddress, implementationSection, maxDepth - 1, true);
                                    }
                                });
                            }
                        }

                        return;
                    }
                    var value_name = value.name.toString();

                    if (value_name === "") {
                        return;
                    }
                    counter += 1;

                    var isPayable = value.payable;
                    var counterInput = 0;
                    var maxItemsInput = value.inputs.length;
                    var inputExtr_WithName = '';

                    if (isPayable) {
                        inputExtr_WithName += ' <div class="form-group"><label>' + value_name + ' </label>' +
                            '<input type="text" class="form-control form-control-xs" id="input_payable_' + value_name + '" name="payable_' + value_name + '" placeholder="&nbsp; payableAmount (ether)"></div>';
                    }


                    var inputId = "input_" + counter;
                    if (isProxy)
                        inputId += "_proxy_" + maxDepth;


                    if (value.inputs.length > 0) {
                        $.each(value.inputs, function (i, v) {
                            counterInput += 1;
                            var inputTag = '';
                            var inputName = v.name.toString();

                            if (v.type.indexOf('][') !== -1) {
                                var regex = /\[([0-9,-]+)\]/;
                                var dynamicArray = v.type.toString().match(regex)[1];
                                var d;
                                inputTag = ' <div class="form-group"><label>' + inputName + ' (' + v.type.toString() + ') </label>';
                                for (d = 0; d < dynamicArray; d++) {


                                  
                                    var counterInputGroup = "g" + counterInput;

                                    if (isProxy) {                                    
                                        counterInputGroup += "_proxy_" + maxDepth;
                                    }
                                       
                                    inputTag += '<input type="text" style="margin-bottom:5px" class="form-control form-control-xs" id="' + inputId + '" name="noname" data-grp="' + counterInputGroup + '" data-type="' + v.type.toString() + '" placeholder="&nbsp; ' + inputName + '[]">';
                                   
                                }

                                inputTag += '</div>';


                            } else {
                               

                                inputTag = GenerateInputTag(inputName, inputId, v.type.toString(), isProxy, maxDepth);
                            }

                            inputExtr_WithName += inputTag;
                        });
                    }


                    inputExtr_WithName += "<button type='button' class='write-btn btn btn-xs btn-primary border' onclick=\"write0('" + value_name + "', '" + inputId + "');\">Write</button> <div style='display:inline' class='write-msg text-success " + inputId + "'></div>";


                    GenerateRow(value_name, inputExtr_WithName, counter, body);

                });

                $('#footer').show();
            }
            $('.write-btn').addClass('disabled');

            var obj = window.parent.document.getElementById('writecontractiframe');
            if (obj !== null)
                parent.resizeIframe(obj, 0);
        });
    }

    function GenerateInputTag(inputName, inputId, type) {
        if (inputName !== "") {
            return ' <div class="form-group"><label>' + inputName + ' (' + type + ') </label>' +
                '<input type="text" class="form-control form-control-xs" id="' + inputId + '" name="noname" data-type="' + type + '" placeholder="&nbsp; ' + inputName + ' (' + type + ')"></div>';

        } else {
            return ' <div class="form-group"><label>' + type + '</label>' +
                '<input type="text" class="form-control form-control-xs" id="' + inputId + '" name="noname" data-type="' + type + '" placeholder=" &nbsp; &lt;input&gt (' + type + ')"></div>';
        }
    }

    function GenerateRow(fieldName, outputFieldsWithName, counter, body) {
        if (!hasInput) {
            hasInput = true;

            header.append('<div class="alert bg-light border"><p class="mb-0"><i class="fas fa-magic text-primary mr-1"></i> <strong>Feature Tip:</strong> <a class="font-weight-bold" href="/dapp/' + contractAddress + '"  target="_parent">Etherscan Dapp Page</a> - A new front-end interface for any smart contract on Ethereum!</p></div>')
            header.append('<div class="d-sm-flex justify-content-between mb-3"><p class="ml-3 mr-3 mb-1"><i id="connector" class="fa fa-circle text-danger mr-1"></i> Write Contract <a id="connectWeb3" style="font-size: 12px!important" href="#" onclick="connectWeb3(); return false;">Connect to Web3</a ></p><a class="ml-3 mr-3" href="?m=' + mode + '&a=' + contractAddress + '&n=' + net + '">[Reset]</a></div >');

        }
        var output = '<div class="card shadow-none mb-3"><div class="card-header bg-light card-collapse p-0" role="tab" id="heading' + counter + '">' +
            '<a role="button" class="btn btn-link btn-block text-dark d-flex justify-content-between align-items-center py-2"  data-toggle="collapse" data-parent="#accordion" href="#collapse' + counter + '" aria-expanded="true" aria-controls="collapse' + counter + '">' + counter + '. ' + fieldName + '<span class="accordion-arrow"><i class="fas fa-arrow-down small"></i></span></a></div>' +
            '<div id="collapse' + counter + '" class="collapse show" role="tabpanel" aria-labelledby="heading' + counter + '"><div class="card-body"><form>' + outputFieldsWithName + '</form></div></div></div>';

        body.before(output);
    }

    function NewProxySection(body, address) {
        let section = '<p>Showing ABI for possible implementation <a href="/address/' + address + '#writeContract" target="_blank" >' + address + '</a></p><div class="panel-group acc-v1" id="impl' + address + '" role="tablist" aria-multiselectable="true"></div>';
        $("#footer").before(section);
        return $('#impl' + address);
    }

    function write0(method, input) {

        if (isAccount === false) {
            alert("Please connect to your Web3 provider!");

            return;
        }


        var functiontoCall = 'myContractInstance.methods.' + method;
        var params = [];
        var ctrl = document.querySelectorAll("[id=" + input + "]");
        var inputs = [];

        for (var i = 0; i < ctrl.length; i++) {
            var type = ctrl[i].getAttribute('data-type');
            var grp = ctrl[i].getAttribute('data-grp');
            var values = [];

            if (ctrl[i].value == '' && grp === null) {
                document.getElementById(input).focus();
                alert('Input value cannot be empty');
                return false;
            }

            var value = strip(ctrl[i].value);
            if (value) {
                if (type.indexOf('[') !== -1 && type.indexOf(']') !== -1) values.push(value.split(','));
                else values.push(value);
            } else values.push('');

            inputs.push({ type: type, value: values, grp: grp });
        }

        var params = encodeParams(inputs);
        var payableAmountInput = document.getElementById("input_payable_" + method);
        var payableParam = payableAmountInput && !isNaN(payableAmountInput.value) ? ', { value: web3.toWei(' + Escape(payableAmountInput.value) + ', "ether") }' : '';

        try {
            new Function(functiontoCall + "(" + params + payableParam + ").send({ from:'" + web3.eth.defaultAccount + "'})" +
                ".on('transactionHash', function(hash) { showTx('', hash, '" + input + "'); })" +
                ".on('error', function(error) { showTx(error, '', '" + input + "') });")();
        } catch (err) {
            showTx(err.message, '', input);
        }

    }

    function encodeParams(values) {
        var params = '';

        if (values.length === 0)
            return undefined;

        for (i = 0; i < values.length; i++) {
            var param = values[i];

            if (param.value !== '') {
                if (param.grp !== null) {
                    var _grp = values.filter(function (x) { return x.grp == param.grp });
                    var _grpParam = '';

                    for (g = 0; g < _grp.length; g++) {
                        param = _grp[g];

                        if (param.value[0] !== '') {
                            if (g == 0)
                                _grpParam = '[' + toHex(param.type, Escape(param.value[0]));
                            else
                                _grpParam = _grpParam + ',' + toHex(param.type, Escape(param.value[0]));
                        }
                    }
                    _grpParam += ']';

                    if (i == 0)
                        params += _grpParam;
                    else
                        params += ',' + _grpParam;

                    i += _grp.length - 1;
                }
                else {
                    if (i == 0)
                        params = toHex(param.type, Escape(param.value[0]));
                    else
                        params = params + ',' + toHex(param.type, Escape(param.value[0]));
                }
            }
        }

        return params;
    }

    function Escape(val) {

        if (typeof val === 'string' || val instanceof String)
            return val.replace(/'/g, "\\u0027");
        else
            return val;

    }

    function strip(val) {


        val = val.replace(/"/g, '');
        val = val.replace('[', '');
        val = val.replace(']', '');


        return val;
    }

    function toHex(type, val) {

        if (Array.isArray(val)) {
            var param = "[";

            var i;
            for (i = 0; i < val.length; i++) {
                if (i == 0)
                    param += toHex(type, val[i]);
                else
                    param = param + ',' + toHex(type, val[i]);
            }
            param += "]";

            return param;

        } else {
            if (type.indexOf('bool') !== -1)
                return JSON.parse(val);
            else if (type.indexOf('address') !== -1)
                return "'" + add0xforAddress(val) + "'"
            else
                return "'" + val + "'"
        }

    };

    function showTx(err, msg, input) {

        if (err) {
            $('.' + input).html("<span class='text-danger'>" + err + "</span>");
        } else {
            var _url = 'etherscan.io';
            if (net !== 'mainnet' && net == 'tobalaba')
                _url = "ewc.etherscan.com";
            else if (net !== 'mainnet')
                _url = net + ".etherscan.io"


            if (msg !== undefined)
                $('.' + input).html("<a class='btn btn-primary' href='//" + _url + "/tx/" + msg + "' target='_blank'> View your transaction</a>");
        }

    }

    async function connectWeb3() {
        var network = 0;

        network = await web3.eth.net.getId();
        netID = network.toString();


        switch (netID) {
            case "1":
                network = 'mainnet';
                break;
            case "2":
                network = 'morden';
                break;
            case "3":
                network = 'ropsten';
                break;
            case "4":
                network = 'rinkeby';
                break;
            case "5":
                network = 'goerli';
                break;
            case "42":
                network = 'kovan';
                break;
            case "246":
                network = 'ecw';
                break;
            default:
                console.log('This is an unknown network.');
        }

        if (network.toLowerCase() !== net.toLowerCase()) {
            alert("Please connect your Web3 to " + net + ' network');
            return false;
        } else {
            if (typeof ethereum !== 'undefined') {
                ethereum.enable().then(function () {
                    getWeb3Accounts();
                });
            } else {
                getWeb3Accounts();
            }
        }

        setTimeout(function () {
            window.parent.writeContractLoaded = true;
            var obj = window.parent.document.getElementById('writecontractiframe');

            if (obj !== null) {
                parent.resizeIframe(obj, 0);
                window.parent.isFrameLoading = false;
                window.parent.document.getElementById('overlayMain').style.display = 'none';
            }
        }, 50);
    }

    function getWeb3Accounts() {
        web3.eth.getAccounts(function (err, accounts) {
            if (err) alert(err + '. Are you sure you are on a secure (SSL / HTTPS) connection?');

            if (accounts.length > 0) {
                address = accounts[0];
                var isAddress = web3.utils.isAddress(address);

                if (isAddress) {

                    var msg = 'Please take note that this is a beta version feature and is provided on an "as is" and "as available" basis. Etherscan does not give any warranties and will not be liable for any loss, direct or indirect through continued use of this feature.';

                    if (confirm(msg)) {
                        $('.write-btn').show();
                        $('#connectWeb3').hide();
                        web3.eth.defaultAccount = accounts[0];

                        myContractInstance = new web3.eth.Contract(ABI, contractAddress);

                        $('#connector').removeClass("text-danger").addClass("text-success");
                        $('#connector').attr('title', 'Connected');

                        $('.write-btn').removeClass("disabled");
                    }

                    isAccount = true;
                }
            } else {
                alert('Please connect to your Web3 provider!');
            }
        });
    }

    function add0xforAddress(_address) {
        _address = _address.trim();
        if (_address.startsWith("0x") == false && _address.length == 40) {
            _address = "0x" + _address;
        }
        return _address;
    }

    function getUrlParameter(sParam) {
        var sPageURL = decodeURIComponent(window.location.search.substring(1)),
            sURLVariables = sPageURL.split('&'),
            sParameterName,
            i;

        for (i = 0; i < sURLVariables.length; i++) {
            sParameterName = sURLVariables[i].split('=');

            if (sParameterName[0] === sParam) {
                return sParameterName[1] === undefined ? true : sParameterName[1];
            }
        }
    }


    setTimeout(function () {
        window.parent.writeContractLoaded = true;
        var obj = window.parent.document.getElementById('writecontractiframe');

        if (obj !== null) {
            parent.resizeIframe(obj, 0);
            window.parent.isFrameLoading = false;
            window.parent.document.getElementById('overlayMain').style.display = 'none';
        }

    }, 50);
    function getParameterByName(name) {
        var url = window.location.href;
        name = name.replace(/[\[\]]/g, "\\$&");
        var regex = new RegExp("[?&]" + name + "(=([^&#]*)|&|#|$)"),
            results = regex.exec(url);
        if (!results) return null;
        if (!results[2]) return '';
        return decodeURIComponent(results[2].replace(/\+/g, " "));
    }

    $(document).ready(function () {
        $(window).keydown(function (event) {
            if (event.keyCode == 13) {
                event.preventDefault();
                return false;
            }
        });
    });
</script>
</html>
